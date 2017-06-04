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

type VariableCallback = (variable: VariableInfo) => void;

interface Scope {
    addVariable(identifier: string, name: ts.PropertyName, blockScoped: boolean, exported: boolean, domain: DeclarationDomain): void;
    addUse(use: VariableUse): void;
    getVariables(): Map<string, VariableInfo>;
    getParent(): Scope;
    getFunctionScope(): Scope;
    end(cb: VariableCallback): void;
    settle(): void;
}

abstract class AbstractScope implements Scope {
    protected _variables = new Map<string, VariableInfo>();
    protected _uses: VariableUse[] = [];

    constructor(private _global: boolean) {}

    public addVariable(identifier: string, name: ts.PropertyName, blockScoped: boolean, exported: boolean, domain: DeclarationDomain) {
        const variables = this._getScope(blockScoped).getVariables();
        let variable = variables.get(identifier);
        if (variable === undefined) {
            variable = {
                domain,
                exported,
                declarations: [name],
                uses: [],
                inGlobalScope: this._global,
            };
            variables.set(identifier, variable);
        } else {
            variable.domain |= domain;
            variable.declarations.push(name);
        }
    }

    public addUse(use: VariableUse) {
        this._uses.push(use);
    }

    public getVariables() {
        return this._variables;
    }

    public abstract getParent(): Scope;

    public getFunctionScope(): Scope {
        return this;
    }

    public end(cb: VariableCallback) {
        for (const use of this._uses) {
            const variable = this._variables.get(use.location.text);
            if (variable !== undefined && variable.domain & use.domain) {
                variable.uses.push(use);
            } else {
                this._addToParent(use);
            }
        }
        this._variables.forEach(cb);
    }

    public settle() { // tslint:disable-line:prefer-function-over-method
        throw new Error('not supported');
    }

    protected _getScope(_blockScoped: boolean): Scope {
        return this;
    }

    protected _addToParent(_use: VariableUse) {} // tslint:disable-line:prefer-function-over-method
}

class RootScope extends AbstractScope {
    public getParent(): never { // tslint:disable-line:prefer-function-over-method
        throw new Error('not supported');
    }
}

class NonRootScope extends AbstractScope {
    constructor(protected _parent: Scope) {
        super(false);
    }

    public getParent() {
        return this._parent;
    }

    protected _addToParent(use: VariableUse) {
        this._parent.addUse(use);
    }
}

class FunctionScope extends NonRootScope {
    constructor(parent: Scope) {
        super(parent);
    }

    public settle() {
        const newUses: VariableUse[] = [];
        for (const use of this._uses) {
            if ((use.domain & UsageDomain.Value) !== 0 && (use.domain & UsageDomain.TypeQuery) === 0) {
                const variable = this._variables.get(use.location.text);
                if (variable !== undefined && variable.domain & use.domain) {
                    variable.uses.push(use);
                } else {
                    this._addToParent(use);
                }
            } else {
                newUses.push(use);
            }
        }
        this._uses = newUses;
    }
}

class FunctionExpressionScope extends NonRootScope {
    private _innerScope = new FunctionScope(this);
    private _nameUses: VariableUse[];

    constructor(private _name: ts.Identifier, parent: Scope) {
        super(parent);
    }

    public end(cb: VariableCallback) {
        this._innerScope.end(cb);
        cb({
            declarations: [this._name],
            domain: DeclarationDomain.Value,
            exported: false,
            uses: this._nameUses,
            inGlobalScope: false,
        });
    }

    public settle() {
        return this._innerScope.settle();
    }

    protected _addToParent(use: VariableUse) {
        if (use.domain & UsageDomain.Value && use.location.text === this._name.text) {
            this._nameUses.push(use);
        } else {
            this._parent.addUse(use);
        }
    }

    protected _getScope() {
        return this._innerScope;
    }
}

class BlockScope extends NonRootScope {
    constructor(private _functionScope: Scope, parent: Scope) {
        super(parent);
    }

    public getFunctionScope() {
        return this._functionScope;
    }

    protected _getScope(blockScoped: boolean) {
        return blockScoped ? this : this._functionScope;
    }
}

export interface VariableInfo {
    domain: DeclarationDomain;
    declarations: ts.PropertyName[];
    exported: boolean;
    uses: VariableUse[];
    inGlobalScope: boolean;
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
        const variableCallback = (variable: VariableInfo) => {
            for (const declaration of variable.declarations)
                this._result.set(declaration, variable);
        };
        this._scope = new RootScope(!ts.isExternalModule(sourceFile));
        const cb = (node: ts.Node): void => {
            const boundary = isScopeBoundary(node);
            if (boundary !== ScopeBoundary.None) {
                if (boundary === ScopeBoundary.Function) {
                    if (isFunctionExpression(node) && node.name !== undefined) {
                        this._scope = new FunctionExpressionScope(node.name, this._scope);
                    } else {
                        if (isFunctionDeclaration(node) && node.body !== undefined) {
                            this._handleDeclaration(node, false, DeclarationDomain.Value);
                        } else if (isEnumDeclaration(node)) {
                            this._handleDeclaration(node, true, DeclarationDomain.Any);
                        } else if (isClassLikeDeclaration(node)) {
                            this._handleDeclaration(node, true, DeclarationDomain.Value | DeclarationDomain.Type);
                        } else if (isModuleDeclaration(node) && node.name.kind === ts.SyntaxKind.Identifier) {
                            this._handleNamespace(<ts.NamespaceDeclaration>node);
                        }
                        this._scope = new FunctionScope(this._scope);
                    }
                } else {
                    this._scope = new BlockScope(this._scope.getFunctionScope(), this._scope);
                }
            } // TODO make this an else-if
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
                    return this._scope.settle();
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
                    this._scope.addUse({domain, location: node});
                return;
            }

            if (boundary) {
                ts.forEachChild(node, cb);
                this._scope.end(variableCallback);
                this._scope = this._scope.getParent();
            } else {
                return ts.forEachChild(node, cb);
            }
        };

        ts.forEachChild(sourceFile, cb);
        this._scope.end(variableCallback);
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
}
