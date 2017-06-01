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
} from '../typeguard';
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
    public usedValues = new Map<string, ts.Identifier[]>();
    public usedTypes = new Map<string, ts.Identifier[]>();
    constructor(functionScope?: Scope) {
        // if no functionScope is provided we are in the process of creating a new function scope, which for consistency links to itself
        this.functionScope = functionScope || this;
    }

    public addVariable(identifier: string, name: ts.PropertyName, blockScoped: boolean, exported: boolean, domain: Domain) {
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

    public addUse(identifier: ts.Identifier, domain: Domain) {
        addToList(identifier, (domain & Domain.Value) ? this.usedValues : this.usedTypes);
    }
}

function addToList(identifier: ts.Identifier, map: Map<string, ts.Identifier[]>) {
    const list = map.get(identifier.text);
    if (list === undefined) {
        map.set(identifier.text, [identifier]);
    } else {
        list.push(identifier);
    }
}

function addToAllList(identifiers: ts.Identifier[], map: Map<string, ts.Identifier[]>) {
    const name = identifiers[0].text;
    const list = map.get(name);
    if (list === undefined) {
        map.set(name, [...identifiers]);
    } else {
        list.push(...identifiers);
    }
}

export interface VariableInfo {
    domain: Domain;
    declarations: ts.PropertyName[];
    exported: boolean;
    uses: VariableUse[];
}

export interface VariableUse {
    domain: Domain;
    location: ts.Identifier;
}

export const enum Domain {
    Value = 1,
    Type = 2,
}

export function getUsageDomain(node: ts.Identifier): Domain | undefined {
    if (isUsedAsType(node))
        return Domain.Type;
    if (isValueUsage(node))
        return Domain.Value;
}

export function isUsedAsType(node: ts.Identifier): boolean {
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

export function isUsedAsValue(node: ts.Identifier): boolean {
    return !isUsedAsType(node) && isValueUsage(node);
}

function isValueUsage(node: ts.Identifier): boolean {
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

export function collectVariableUsage(sourceFile: ts.SourceFile) {
    return new UsageWalker().getUsage(sourceFile);
}

class UsageWalker {
    private _result = new Map<ts.PropertyName, VariableInfo>();
    private _scope: Scope;
    public getUsage(sourceFile: ts.SourceFile) {
        this._scope = new Scope();
        const cb = (node: ts.Node): void => {
            const savedScope = this._scope;
            const boundary = isScopeBoundary(node);
            if (boundary !== ScopeBoundary.None) {
                if (boundary === ScopeBoundary.Function) {
                    if (isFunctionExpression(node) && node.name !== undefined) {
                        // special handling for function expression
                        // named function expressions are only available inside the function, but declared variables shadow the name
                        // instead of merging
                        // therefore we need to add another scope layer only for the name of the function expression
                        const scope = this._scope;
                        const functionScope = this._scope = new Scope();
                        this._scope.addVariable(node.name.text, node.name, false, false, Domain.Value);
                        this._scope = new Scope();
                        ts.forEachChild(node, cb);
                        this._onScopeEnd(functionScope);
                        this._onScopeEnd(scope);
                        return;
                    }
                    if (isFunctionDeclaration(node) && node.body !== undefined) {
                        this._handleDeclaration(node, false, Domain.Value);
                    } else if (isEnumDeclaration(node)) {
                        this._handleDeclaration(node, true, Domain.Type | Domain.Type);
                    } else if (isClassLikeDeclaration(node)) {
                        this._handleDeclaration(node, true, Domain.Value & Domain.Type);
                    } else if (isModuleDeclaration(node) && node.name.kind === ts.SyntaxKind.Identifier) {
                        this._handleNamespace(<ts.NamespaceDeclaration>node);
                    }
                    this._scope = new Scope();
                } else {
                    this._scope = new Scope(this._scope.functionScope);
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
                    return this._settle(savedScope);
                }
            } else if (isEnumMember(node)) {
                this._scope.addVariable(getPropertyName(node.name)!, node.name, false, true, Domain.Value);
            } else if (isImportClause(node) || isImportSpecifier(node) || isNamespaceImport(node) || isImportEqualsDeclaration(node)) {
                this._handleDeclaration(node, false, Domain.Type | Domain.Value);
            } else if (isInterfaceDeclaration(node) || isTypeAliasDeclaration(node) || isTypeParameterDeclaration(node)) {
                this._handleDeclaration(node, true, Domain.Type);
            } else if (isIdentifier(node)) {
                const domain = getUsageDomain(node);
                if (domain !== undefined)
                    this._scope.addUse(node, domain);
            }

            if (boundary) {
                ts.forEachChild(node, cb);
                this._onScopeEnd(savedScope);
            } else {
                return ts.forEachChild(node, cb);
            }
        };

        ts.forEachChild(sourceFile, cb);
        if (ts.isExternalModule(sourceFile))
            this._onScopeEnd();
        return this._result;
    }

    private _handleNamespace(node: ts.NamespaceDeclaration) {
        this._scope.addVariable(
            node.name.text,
            node.name,
            false,
            node.parent!.kind === ts.SyntaxKind.ModuleDeclaration || hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword),
            Domain.Value);
    }

    private _handleDeclaration(node: ts.NamedDeclaration, blockScoped: boolean, domain: Domain ) {
        if (node.name !== undefined)
            this._scope.addVariable((<ts.Identifier>node.name).text, <ts.Identifier>node.name, blockScoped,
                                    hasModifier(node.modifiers, ts.SyntaxKind.ExportKeyword), domain);
    }

    private _handleBindingName(name: ts.BindingName,
                               blockScoped: boolean,
                               exported: boolean) {
        if (name.kind === ts.SyntaxKind.Identifier) {
            this._scope.addVariable(name.text, name, blockScoped, exported, Domain.Value);
        } else {
            forEachDestructuringIdentifier(name, (declaration) => {
                this._scope.addVariable(declaration.name.text, declaration.name, blockScoped, exported, Domain.Value);
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

    private _onScopeEnd(parent?: Scope) {
        this._settle(parent);
        const {variables, usedTypes} = this._scope;
        usedTypes.forEach((uses, name) => {
            const variable = variables.get(name);
            if (variable !== undefined && variable.domain & Domain.Type) {
                for (const use of uses)
                    variable.uses.push( {
                        domain: Domain.Type,
                        location: use,
                    });
            } else if (parent !== undefined && uses.length !== 0) {
                addToAllList(uses, parent.usedTypes);
            }
        });
        variables.forEach((value) => {
            for (const declaration of value.declarations)
                this._result.set(declaration, value);
        });
        if (parent !== undefined)
            this._scope = parent;
    }

    private _settle(parent?: Scope) {
        const {variables, usedValues} = this._scope;
        usedValues.forEach((uses, name) => {
            const variable = variables.get(name);
            if (variable !== undefined && variable.domain & Domain.Value) {
                for (const use of uses)
                    variable.uses.push( {
                        domain: Domain.Value,
                        location: use,
                    });
            } else if (parent !== undefined && uses.length !== 0) {
                addToAllList(uses, parent.usedValues);
            }
        });
        usedValues.clear();
    }
}
