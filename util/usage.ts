import {
    isInterfaceDeclaration,
    isParameterDeclaration,
    isTypeAliasDeclaration,
    isTypeParameterDeclaration,
    isEnumMember,
    isFunctionDeclaration,
    isFunctionExpression,
    isModuleDeclaration,
    isClassLikeDeclaration,
    isEnumDeclaration,
    isIdentifier,
    isImportClause,
    isImportEqualsDeclaration,
    isImportSpecifier,
    isNamespaceImport,
    isQualifiedName,
} from '../typeguard/node';
import {
    forEachDestructuringIdentifier,
    isParameterProperty,
    getPropertyName,
    isBlockScopedVariableDeclarationList,
    isScopeBoundary,
    ScopeBoundary,
    hasModifier,
    isFunctionWithBody,
} from './util';
import * as ts from 'typescript';

// TODO handle open ended namespaces and enums
// TODO special handling of anything exported from namespace?
// TODO handle use before delcare in typeof for parameters:
// function fn(foo: typeof bar, bar: typeof baz, baz: typeof bas) {
//     let bas: boolean;
// }

class Scope {
    public functionScope: Scope;
    public variables = new Map<string, VariableInfo>();
    public uses: VariableUse[] = [];
    constructor(public parent?: Scope, functionScope?: Scope) {
        // if no functionScope is provided we are in the process of creating a new function scope, which for consistency links to itself
        this.functionScope = functionScope || this;
    }

    public addVariable(identifier: string, name: ts.PropertyName, blockScoped: boolean, exported: boolean, domain: DeclarationDomain) {
        const scope = blockScoped ? this : this.functionScope;
        let variable = scope.variables.get(identifier);
        if (variable === undefined) {
            variable = {
                domain,
                exported,
                declarations: [name],
                uses: [],
            };
            scope.variables.set(identifier, variable);
        } else {
            variable.domain |= domain;
            variable.declarations.push(name);
        }
    }

    public addUse(location: ts.Identifier, domain: UsageDomain) {
        this.uses.push({location, domain});
    }
}

export interface VariableInfo {
    domain: DeclarationDomain;
    declarations: ts.PropertyName[];
    exported: boolean;
    uses: VariableUse[];
    inGlobalScope?: boolean;
}

export interface VariableUse {
    domain: UsageDomain;
    location: ts.Identifier;
}

export const enum DeclarationDomain {
    Namespace = 1,
    Type = 2,
    Value = 4,
    Any = Namespace | Type | Value,
}

export const enum UsageDomain {
    Namespace = 1,
    Type = 2,
    Value = 4,
    ValueOrNamespace = 5,
    TypeQuery = 8,
}

function getEntityNameParent(name: ts.EntityName) {
    let parent = name.parent!;
    while (parent.kind === ts.SyntaxKind.QualifiedName)
        parent = parent.parent!;
    return parent;
}

function isQualifiedNameStart(name: ts.QualifiedName, node: ts.Identifier): boolean {
    if (name.right === node)
        return false;
    let parent = name.parent!;
    while (isQualifiedName(parent)) {
        if (parent.right === node)
            return false;
        name = parent;
        parent = name.parent!;
    }
    return true;
}

export function getUsageDomain(node: ts.Identifier): UsageDomain | undefined {
    if (isUsedAsType(node))
        return UsageDomain.Type;
    if (node.parent!.kind === ts.SyntaxKind.TypeQuery)
        return UsageDomain.Value | UsageDomain.TypeQuery;
    if (isUsedAsValue(node))
        return UsageDomain.ValueOrNamespace;
    if (node.parent!.kind === ts.SyntaxKind.QualifiedName && isQualifiedNameStart(<ts.QualifiedName>node.parent, node))
        return UsageDomain.Namespace |
            (getEntityNameParent(<ts.QualifiedName>node.parent).kind === ts.SyntaxKind.TypeQuery ? UsageDomain.TypeQuery : 0);
    if (node.parent!.kind === ts.SyntaxKind.NamespaceExportDeclaration)
        return UsageDomain.Namespace;
}

function isUsedAsType(node: ts.Identifier): boolean {
    const parent = node.parent!;
    switch (parent.kind) {
        case ts.SyntaxKind.TypeReference:
        case ts.SyntaxKind.TypeOperator:
            return true;
        case ts.SyntaxKind.ExpressionWithTypeArguments:
            return (<ts.HeritageClause>parent.parent).token === ts.SyntaxKind.ImplementsKeyword ||
                parent.parent!.parent!.kind === ts.SyntaxKind.InterfaceDeclaration;
        default:
            return false;
    }
}

function isUsedAsValue(node: ts.Identifier): boolean {
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
        case ts.SyntaxKind.ImportClause:
        case ts.SyntaxKind.ImportSpecifier:
        case ts.SyntaxKind.TypePredicate:
        case ts.SyntaxKind.MethodSignature:
        case ts.SyntaxKind.PropertySignature:
        case ts.SyntaxKind.NamespaceExportDeclaration:
        case ts.SyntaxKind.QualifiedName:
        case ts.SyntaxKind.TypeReference:
        case ts.SyntaxKind.TypeOperator:
            return false;
        default:
            return true;
    }
}

export function collectVariableUsage(sourceFile: ts.SourceFile) {
    return new UsageWalker().getUsage(sourceFile);
}

class UsageWalker {
    private _result = new Map<ts.PropertyName, VariableInfo>();
    private _scope: Scope;
    public getUsage(sourceFile: ts.SourceFile) {
        this._scope = new Scope();
        const cb = (node: ts.Node): void => {
            const boundary = isScopeBoundary(node);
            if (boundary !== ScopeBoundary.None) {
                if (boundary === ScopeBoundary.Function) {
                    if (isFunctionExpression(node) && node.name !== undefined) {
                        // special handling for function expression
                        // named function expressions are only available inside the function, but declared variables shadow the name
                        // instead of merging
                        // therefore we need to add another scope layer only for the name of the function expression
                        this._scope = new Scope(this._scope);
                        this._scope.addVariable(node.name.text, node.name, false, false, DeclarationDomain.Value);
                        this._scope = new Scope(this._scope);
                        ts.forEachChild(node, cb);
                        this._onScopeEnd();
                        this._onScopeEnd();
                        return;
                    }
                    if (isFunctionDeclaration(node) && node.body !== undefined) {
                        this._handleDeclaration(node, false, DeclarationDomain.Value);
                    } else if (isEnumDeclaration(node)) {
                        this._handleDeclaration(node, true, DeclarationDomain.Any);
                    } else if (isClassLikeDeclaration(node)) {
                        this._handleDeclaration(node, true, DeclarationDomain.Value | DeclarationDomain.Type);
                    } else if (isModuleDeclaration(node) && node.name.kind === ts.SyntaxKind.Identifier) {
                        this._handleNamespace(<ts.NamespaceDeclaration>node);
                    }
                    this._scope = new Scope(this._scope);
                } else {
                    this._scope = new Scope(this._scope, this._scope.functionScope);
                }
            }
            if (node.kind === ts.SyntaxKind.VariableDeclarationList) {
                this._handleVariableDeclaration(<ts.VariableDeclarationList>node);
            } else if (node.kind === ts.SyntaxKind.CatchClause) {
                this._handleBindingName((<ts.CatchClause>node).variableDeclaration.name, true, true);
            } else if (isParameterDeclaration(node)) {
                const parent = node.parent!;
                // don't handle parameters of overloads or other signatures
                if (isFunctionWithBody(parent) &&
                     // exclude this parameter
                    (node.name.kind !== ts.SyntaxKind.Identifier || node.name.originalKeywordKind !== ts.SyntaxKind.ThisKeyword)) {
                    this._handleBindingName(node.name, false, isParameterProperty(node));
                    // special handling for parameters
                    // each parameter initializer can only access preceding parameters, therefore we need to settle after each one
                    ts.forEachChild(node, cb);
                    return this._settle();
                }
            } else if (isEnumMember(node)) {
                this._scope.addVariable(getPropertyName(node.name)!, node.name, false, true, DeclarationDomain.Value);
            } else if (isImportClause(node) || isImportSpecifier(node) || isNamespaceImport(node) || isImportEqualsDeclaration(node)) {
                this._handleDeclaration(node, false, DeclarationDomain.Any);
            } else if (isInterfaceDeclaration(node) || isTypeAliasDeclaration(node) || isTypeParameterDeclaration(node)) {
                this._handleDeclaration(node, true, DeclarationDomain.Type);
            } else if (isIdentifier(node)) {
                const domain = getUsageDomain(node);
                if (domain !== undefined)
                    this._scope.addUse(node, domain);
            }

            if (boundary) {
                ts.forEachChild(node, cb);
                this._onScopeEnd();
            } else {
                return ts.forEachChild(node, cb);
            }
        };

        ts.forEachChild(sourceFile, cb);
        this._onScopeEnd(!ts.isExternalModule(sourceFile));
        return this._result;
    }

    private _handleNamespace(node: ts.NamespaceDeclaration) {
        this._scope.addVariable(
            node.name.text,
            node.name,
            false,
            node.parent!.kind === ts.SyntaxKind.ModuleDeclaration || hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword),
            DeclarationDomain.Namespace);
    }

    private _handleDeclaration(node: ts.NamedDeclaration, blockScoped: boolean, domain: DeclarationDomain ) {
        if (node.name !== undefined)
            this._scope.addVariable((<ts.Identifier>node.name).text, <ts.Identifier>node.name, blockScoped,
                                    hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword), domain);
    }

    private _handleBindingName(name: ts.BindingName,
                               blockScoped: boolean,
                               exported: boolean) {
        if (name.kind === ts.SyntaxKind.Identifier) {
            this._scope.addVariable(name.text, name, blockScoped, exported, DeclarationDomain.Value);
        } else {
            forEachDestructuringIdentifier(name, (declaration) => {
                this._scope.addVariable(declaration.name.text, declaration.name, blockScoped, exported, DeclarationDomain.Value);
            });
        }
    }

    private _handleVariableDeclaration(declarationList: ts.VariableDeclarationList) {
        const blockScoped = isBlockScopedVariableDeclarationList(declarationList);
        const exported = declarationList.parent!.kind === ts.SyntaxKind.VariableStatement &&
            hasModifier(declarationList.parent!.modifiers, ts.SyntaxKind.ExportKeyword);
        for (const declaration of declarationList.declarations)
            this._handleBindingName(declaration.name, blockScoped, exported);
    }

    private _onScopeEnd(global?: boolean) {
        const {variables, uses, parent} = this._scope;
        for (const use of uses) {
            const variable = variables.get(use.location.text);
            if (variable !== undefined && variable.domain & use.domain) {
                variable.uses.push(use);
            } else if (parent !== undefined) {
                parent.uses.push(use);
            }
        }
        variables.forEach((variable) => {
            variable.inGlobalScope = global;
            for (const declaration of variable.declarations)
                this._result.set(declaration, variable);
        });
        if (parent !== undefined)
            this._scope = parent;
    }

    private _settle() {
        const {variables, uses, parent} = this._scope;
        const newUses: VariableUse[] = [];
        for (const use of uses) {
            if ((use.domain & UsageDomain.Value) !== 0 && (use.domain & UsageDomain.TypeQuery) === 0) {
                const variable = variables.get(use.location.text);
                if (variable !== undefined && variable.domain & use.domain) {
                    variable.uses.push(use);
                } else {
                    parent!.uses.push(use);
                }
            } else {
                newUses.push(use);
            }
        }
        this._scope.uses = newUses;
    }
}
