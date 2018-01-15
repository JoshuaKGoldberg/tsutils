import * as ts from 'typescript';
import { isBlockLike, isBreakOrContinueStatement, isBreakStatement } from '../typeguard/node';

export function endsControlFlow(statement: ts.Statement | ts.BlockLike): boolean {
    return getControlFlowEnd(statement).end;
}

export type ControlFlowStatement = ts.BreakStatement | ts.ContinueStatement | ts.ReturnStatement | ts.ThrowStatement;
export interface ControlFlowEnd {
    /**
     * Statements that may end control flow at this statement.
     * Does not contain control flow statements that jump only inside the statement, for example a `continue` inside a nested for loop.
     */
    statements: ControlFlowStatement[];
    /** `true` if control flow definitely ends. */
    end: boolean;
}

const defaultControlFlowEnd: ControlFlowEnd = {statements: [], end: false};

export function getControlFlowEnd(statement: ts.Statement | ts.BlockLike): ControlFlowEnd;
/** @deprecated passing label no longer has any effect. */
export function getControlFlowEnd(statement: ts.Statement | ts.BlockLike, label?: ts.Identifier): ControlFlowEnd; // tslint:disable-line
export function getControlFlowEnd(statement: ts.Statement | ts.BlockLike): ControlFlowEnd {
    return isBlockLike(statement) ? handleBlock(statement) : getControlFlowEndWorker(statement);
}

function getControlFlowEndWorker(statement: ts.Statement): ControlFlowEnd {
    switch (statement.kind) {
        case ts.SyntaxKind.ReturnStatement:
        case ts.SyntaxKind.ThrowStatement:
        case ts.SyntaxKind.ContinueStatement:
        case ts.SyntaxKind.BreakStatement:
            return {statements: [<ControlFlowStatement>statement], end: true};
        case ts.SyntaxKind.Block:
            return handleBlock(<ts.Block>statement);
        case ts.SyntaxKind.ForStatement:
        case ts.SyntaxKind.ForOfStatement:
        case ts.SyntaxKind.ForInStatement:
        case ts.SyntaxKind.DoStatement:
        case ts.SyntaxKind.WhileStatement:
            return matchBreakOrContinue(getControlFlowEndWorker((<ts.IterationStatement>statement).statement), isBreakOrContinueStatement);
        case ts.SyntaxKind.IfStatement:
            return handleIfStatement(<ts.IfStatement>statement);
        case ts.SyntaxKind.SwitchStatement:
            return matchBreakOrContinue(handleSwitchStatement(<ts.SwitchStatement>statement), isBreakStatement);
        case ts.SyntaxKind.TryStatement:
            return handleTryStatement(<ts.TryStatement>statement);
        case ts.SyntaxKind.LabeledStatement:
            return matchLabel(getControlFlowEndWorker((<ts.LabeledStatement>statement).statement), (<ts.LabeledStatement>statement).label);
        case ts.SyntaxKind.WithStatement:
            return getControlFlowEndWorker((<ts.WithStatement>statement).statement);
        default:
            return defaultControlFlowEnd;
    }
}

function handleBlock(statement: ts.BlockLike): ControlFlowEnd {
    const result: ControlFlowEnd = {statements: [], end: false};
    for (const s of statement.statements) {
        const current = getControlFlowEndWorker(s);
        result.statements.push(...current.statements);
        if (current.end) {
            result.end = true;
            break;
        }
    }
    return result;
}

function handleIfStatement(node: ts.IfStatement): ControlFlowEnd {
    const then = getControlFlowEndWorker(node.thenStatement);
    if (node.elseStatement === undefined) {
        then.end = false;
        return then;
    }
    const elze = getControlFlowEndWorker(node.elseStatement);
    return {
        statements: then.statements.concat(elze.statements),
        end: then.end && elze.end,
    };
}

function handleSwitchStatement(node: ts.SwitchStatement): ControlFlowEnd {
    let hasDefault = false;
    const result: ControlFlowEnd = {
        statements: [],
        end: false,
    };
    for (const clause of node.caseBlock.clauses) {
        if (clause.kind === ts.SyntaxKind.DefaultClause)
            hasDefault = true;
        const current = handleBlock(clause);
        result.end = current.end;
        result.statements.push(...current.statements);
    }
    if (!hasDefault)
        result.end = false;
    return result;
}

function handleTryStatement(node: ts.TryStatement): ControlFlowEnd {
    let finallyResult: ControlFlowEnd | undefined;
    if (node.finallyBlock !== undefined) {
        finallyResult = handleBlock(node.finallyBlock);
        // if 'finally' always ends control flow, we are not interested in any jump statements from 'try' or 'catch'
        if (finallyResult.end)
            return finallyResult;
    }
    const tryResult = handleBlock(node.tryBlock);
    if (node.catchClause === undefined)
        return finallyResult === undefined
            ? tryResult
            : {statements: finallyResult.statements.concat(tryResult.statements), end: tryResult.end};

    const catchResult = handleBlock(node.catchClause.block);
    return {
        statements: tryResult.statements
            // remove all throw statements from the list of control flow statements inside tryBlock
            .filter((s) => s.kind !== ts.SyntaxKind.ThrowStatement)
            .concat(catchResult.statements, finallyResult === undefined ? [] : finallyResult.statements),
        end: tryResult.end && catchResult.end, // only ends control flow if try AND catch definitely end control flow
    };
}

function matchBreakOrContinue(current: ControlFlowEnd, pred: typeof isBreakOrContinueStatement): ControlFlowEnd {
    const result: ControlFlowEnd = {
        statements: [],
        end: current.end,
    };
    for (const statement of current.statements) {
        if (pred(statement) && statement.label === undefined) {
            result.end = false;
            continue;
        }
        result.statements.push(statement);
    }
    return result;
}

function matchLabel(current: ControlFlowEnd, label: ts.Identifier) {
    const result: ControlFlowEnd = {
        statements: [],
        end: current.end,
    };
    const labelText = label.text;
    for (const statement of current.statements) {
        switch (statement.kind) {
            case ts.SyntaxKind.BreakStatement:
            case ts.SyntaxKind.ContinueStatement:
                if (statement.label !== undefined && statement.label.text === labelText) {
                    result.end = false;
                    continue;
                }
        }
        result.statements.push(statement);
    }
    return result;
}
