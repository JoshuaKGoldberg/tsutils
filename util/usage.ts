import {
    isInterfaceDeclaration,
    isParameterDeclaration,
    isTypeAliasDeclaration,
    isTypeParameterDeclaration,
    isEnumMember,
    isFunctionDeclaration,
    isFunctionExpression,
    isMethodDeclaration,
    isClassLikeDeclaration,
    isEnumDeclaration,
    isIdentifier,
    isImportClause,
    isImportEqualsDeclaration,
    isImportSpecifier,
    isNamespaceImport,
} from '../typeguard';
import {
    forEachDestructuringIdentifier,
    isParameterProperty,
    getPropertyName,
    isBlockScopedVariableDeclarationList,
    isJsDocKind,
    isScopeBoundary,
    ScopeBoundary,
    hasModifier,
} from './util';
import * as ts from 'typescript';

// TODO handle open ended namespaces and enums
// TODO special handling of anything exported from namespace?

class Scope {
    public functionScope: Scope;
    public variables = new Map<string, VariableInfo>();
    public types = new Map<string, TypeInfo>();
    public usedVariables = new Set<string>();
    public usedTypes = new Set<string>();
    constructor(functionScope?: Scope) {
        // if no functionScope is provided we are in the process of creating a new function scope, which for consistency links to itself
        this.functionScope = functionScope || this;
    }

    public addVariable(identifier: string, name: ts.PropertyName, blockScoped: boolean, info: AdditionalVariableInfo) {
        const scope = blockScoped ? this : this.functionScope;
        scope.variables.set(identifier, {
            name,
            info,
            used: false,
        });
    }

    public addType(name: ts.Identifier, info: AdditionalTypeInfo) {
        this.types.set(name.text, {
            name,
            info,
            used: false,
        });
    }
}

interface VariableInfo {
    name: ts.PropertyName;
    info: AdditionalVariableInfo;
    used: boolean;
}

interface TypeInfo {
    name: ts.Identifier;
    info: AdditionalTypeInfo;
    used: boolean;
}

interface AdditionalVariableInfo {
    type: 'import' | 'variable' | 'parameter' | 'class' | 'function' | 'enum' | 'namespace' | 'enumMember';
    exported: boolean;
}

interface AdditionalTypeInfo {
    type: 'import' | 'class' | 'typeParameter' | 'interface' | 'type' | 'enum';
    exported: boolean;
}

const enum UsageDomain {
    None,
    Type,
    Variable,
}

function getUsageDomain(node: ts.Identifier): UsageDomain {
    if (isTypeUsage(node))
        return UsageDomain.Type;
    if (isVariableUsage(node))
        return UsageDomain.Variable;
    return UsageDomain.None;
}

function isTypeUsage(node: ts.Identifier): boolean {
    const parent = node.parent!;
    switch (parent.kind) {
        case ts.SyntaxKind.TypeReference:
        case ts.SyntaxKind.TypeOperator:
            return true;
        case ts.SyntaxKind.ExpressionWithTypeArguments:
            return (<ts.HeritageClause>parent.parent).token === ts.SyntaxKind.ImplementsKeyword ||
                parent.parent!.parent!.kind === ts.SyntaxKind.InterfaceDeclaration;
        case ts.SyntaxKind.QualifiedName:
            return (<ts.QualifiedName>parent).right !== node;
        default:
            return false;
    }
}

function isVariableUsage(node: ts.Identifier): boolean {
    const parent = node.parent!;
    switch (parent.kind) {
        case ts.SyntaxKind.BindingElement:
            return (<ts.BindingElement>parent).initializer === node;
        case ts.SyntaxKind.ExportSpecifier:
            // either {name} or {propertyName as name}
            return (<ts.ExportSpecifier>parent).propertyName === undefined ||
                (<ts.ExportSpecifier>parent).propertyName === node;
        case ts.SyntaxKind.ExpressionWithTypeArguments:
            return (<ts.HeritageClause>parent.parent).token === ts.SyntaxKind.ExtendsKeyword &&
                parent.parent!.parent!.kind !== ts.SyntaxKind.InterfaceDeclaration;
        case ts.SyntaxKind.EnumMember:
        case ts.SyntaxKind.PropertyDeclaration:
        case ts.SyntaxKind.Parameter:
        case ts.SyntaxKind.VariableDeclaration:
        case ts.SyntaxKind.PropertyAssignment:
        case ts.SyntaxKind.PropertyAccessExpression:
        case ts.SyntaxKind.ImportEqualsDeclaration:
        case ts.SyntaxKind.TypeParameter:
            return (<ts.Declaration>parent).name !== node;
        case ts.SyntaxKind.JsxAttribute:
        case ts.SyntaxKind.FunctionDeclaration:
        case ts.SyntaxKind.FunctionExpression:
        case ts.SyntaxKind.NamespaceImport:
        case ts.SyntaxKind.ClassDeclaration:
        case ts.SyntaxKind.ClassExpression:
        case ts.SyntaxKind.ModuleDeclaration:
        case ts.SyntaxKind.MethodDeclaration:
        case ts.SyntaxKind.EnumDeclaration:
        case ts.SyntaxKind.GetAccessor:
        case ts.SyntaxKind.SetAccessor:
        case ts.SyntaxKind.LabeledStatement:
        case ts.SyntaxKind.NamespaceImport:
        case ts.SyntaxKind.ImportClause:
        case ts.SyntaxKind.ImportSpecifier:
        case ts.SyntaxKind.TypePredicate:
        case ts.SyntaxKind.MethodSignature:
        case ts.SyntaxKind.PropertySignature:
        case ts.SyntaxKind.NamespaceExportDeclaration:
        case ts.SyntaxKind.QualifiedName:
            return false;
        default:
            return true;
    }
}

class UnusedWalker {
    private _scope: Scope;
    public walk(sourceFile: ts.SourceFile) {
        this._scope = new Scope();
        const cb = (node: ts.Node): void => {
            if (isJsDocKind(node.kind))
                return;
            const savedScope = this._scope;
            const boundary = isScopeBoundary(node);
            if (boundary !== ScopeBoundary.None) {
                if (boundary === ScopeBoundary.Function) {
                    if (isFunctionDeclaration(node) && node.body !== undefined ||
                        isFunctionExpression(node)) {
                        this._handleDeclaration(node, false, 'function');
                    } else if (isEnumDeclaration(node)) {
                        this._handleDeclaration(node, true, 'enum');
                    } else if (isClassLikeDeclaration(node)) {
                        this._handleDeclaration(node, true, 'class');
                    }// else if (isModuleDeclaration(node) && node.name.kind === ts.SyntaxKind.Identifier)
                     //       this._handleDeclaration(node, false, 'namespace');
                    this._scope = new Scope();
                } else {
                    this._scope = new Scope(this._scope.functionScope);
                }
            }
            if (node.kind === ts.SyntaxKind.VariableDeclarationList) {
                this._handleVariableDeclaration(<ts.VariableDeclarationList>node);
            } else if (node.kind === ts.SyntaxKind.CatchClause) {
                this._handleBindingName((<ts.CatchClause>node).variableDeclaration.name, true, 'variable', true);
            } else if (isParameterDeclaration(node)) {
                const parent = node.parent!;
                // don't handle parameters of overloads or other signatures
                if (((isMethodDeclaration(parent) || isFunctionDeclaration(parent)) && parent.body !== undefined ||
                     parent.kind === ts.SyntaxKind.FunctionExpression) &&
                     // exclude this parameter
                    (node.name.kind !== ts.SyntaxKind.Identifier || node.name.originalKeywordKind !== ts.SyntaxKind.ThisKeyword) ||
                    parent.kind === ts.SyntaxKind.ArrowFunction ||
                    parent.kind === ts.SyntaxKind.Constructor) {
                    this._handleBindingName(node.name, false, 'parameter', isParameterProperty(node));
                    // special handling for parameters
                    // each parameter initializer can only access preceding parameters, therefore we need to settle after each one
                    ts.forEachChild(node, cb);
                    return this._settle(savedScope);
                }
            } else if (isEnumMember(node)) {
                this._scope.addVariable(getPropertyName(node.name)!, node.name, false, {
                    type: 'enumMember',
                    exported: true,
                });
            } else if (isImportClause(node) || isImportSpecifier(node) || isNamespaceImport(node) || isImportEqualsDeclaration(node)) {
                this._handleDeclaration(node, false, 'import');
            } else if (isInterfaceDeclaration(node) || isTypeAliasDeclaration(node) || isTypeParameterDeclaration(node)) {
                this._handleType(node);
            } else if (isIdentifier(node)) {
                switch (getUsageDomain(node)) {
                    case UsageDomain.Variable:
                        this._scope.usedVariables.add(node.text);
                        break;
                    case UsageDomain.Type:
                        this._scope.usedTypes.add(node.text);
                        break;
                }
            }

            if (boundary) {
                ts.forEachChild(node, cb);
                this._onScopeEnd(savedScope);
            } else {
                return ts.forEachChild(node, cb);
            }
        };

        if (ts.isExternalModule(sourceFile)) {
            ts.forEachChild(sourceFile, cb);
            this._onScopeEnd();
        } else {
            return ts.forEachChild(sourceFile, cb);
        }
    }

    private _handleDeclaration(node: ts.FunctionDeclaration | ts.FunctionExpression | ts.EnumDeclaration | ts.ClassLikeDeclaration |
                                     ts.ImportClause | ts.ImportSpecifier | ts.NamespaceImport | ts.ImportEqualsDeclaration,
                               blockScoped: boolean,
                               type: 'enum' | 'class' | 'function' | 'import' ) {
        if (node.name !== undefined) {
            this._scope.addVariable(node.name.text, node.name, blockScoped, {
                type,
                exported: hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword),
            });
            if (isCrossDomain(type))
                this._scope.addType(node.name, {
                    type,
                    exported: hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword),
                });
        }
    }

    private _handleType(node: ts.TypeAliasDeclaration | ts.InterfaceDeclaration | ts.TypeParameterDeclaration) {
        let type: 'type' | 'typeParameter' | 'interface';
        switch (node.kind) {
            case ts.SyntaxKind.InterfaceDeclaration:
                type = 'interface';
                break;
            case ts.SyntaxKind.TypeParameter:
                type = 'typeParameter';
                break;
            default:
                type = 'type';
                break;
        }
        this._scope.addType(node.name, {
            type,
            exported: hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword) ||
                node.kind === ts.SyntaxKind.TypeParameter && node.parent!.kind === ts.SyntaxKind.MappedType,
        });
    }

    private _handleBindingName(name: ts.BindingName,
                               blockScoped: boolean,
                               type: 'variable' | 'parameter',
                               exported: boolean) {
        if (name.kind === ts.SyntaxKind.Identifier) {
            this._scope.addVariable(name.text, name, blockScoped, {
                type,
                exported,
            });
        } else {
            forEachDestructuringIdentifier(name, (declaration) => {
                this._scope.addVariable(declaration.name.text, declaration.name, blockScoped, {
                    exported,
                    type: 'variable',
                });
            });
        }
    }

    private _handleVariableDeclaration(declarationList: ts.VariableDeclarationList) {
        const blockScoped = isBlockScopedVariableDeclarationList(declarationList);
        const exported = declarationList.parent!.kind === ts.SyntaxKind.VariableStatement &&
            hasModifier(declarationList.parent!.modifiers, ts.SyntaxKind.ExportKeyword);
        for (const declaration of declarationList.declarations) {
            this._handleBindingName(declaration.name, blockScoped, 'variable', exported);
        }
    }

    private _onScopeEnd(parent?: Scope) {
        this._settle(parent);
        this._scope.variables.forEach((variable, name) => {
            if (!variable.used &&
                !variable.info.exported)
                this.addFailureAtNode(variable.name, `Unused ${variable.info.type}: '${name}'`);
        });
        this._scope.types.forEach((type, name) => {
            if (!type.used &&
                !type.info.exported &&
                !isCrossDomain(type.info.type))
                this.addFailureAtNode(type.name, `Unused ${type.info.type}: '${name}'`);
        });
        if (parent !== undefined)
            this._scope = parent;
    }

    private _settle(parent?: Scope) {
        const {variables, types, usedVariables, usedTypes} = this._scope;
        usedTypes.forEach((name) => {
            const type = types.get(name);
            if (type !== undefined) {
                type.used = true;
                if (isCrossDomain(type.info.type))
                    variables.get(name)!.used = true;
            } else if (parent !== undefined) {
                parent.usedTypes.add(name);
            }
        });
        usedVariables.forEach((name) => {
            const variable = variables.get(name);
            if (variable !== undefined) {
                variable.used = true;
                if (isCrossDomain(variable.info.type))
                    types.get(name)!.used = true;
            } else if (parent !== undefined) {
                parent.usedVariables.add(name);
            }
        });
        usedVariables.clear();
    }
}

function isCrossDomain(type: string): type is 'class' | 'enum' | 'import' {
    switch (type) {
        case 'class':
        case 'enum':
        case 'import':
            return true;
        default:
            return false;
    }
}
