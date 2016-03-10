/*
 * Copyright 2015 Samsung Information Systems America, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Author: Esben Andreasen

var jalangiInterface = require("../src/JalangiInterface");
var astUtil = jalangiInterface.astUtil,
    transformAst = astUtil.transformAst,
    jalangiASTQueries = require('./jalangiASTQueries');

var isJalangiCall = jalangiASTQueries.isJalangiCall,
    unwrapJalangiIgnoreAndAssignCall = jalangiASTQueries.unwrapJalangiIgnoreAndAssignCall,
    getIIDOfJalangiCall = jalangiASTQueries.getIIDOfJalangiCall,
    getArgumentsToJalangiCall = jalangiASTQueries.getArgumentsToJalangiCall,
    isIndirectJalangiCall = jalangiASTQueries.isIndirectJalangiCall;

/**
 * given an instrumented AST, returns an array of pairs of IIDs and booleans for recovering the locations of the desugared && and || expresions
 * e.g. `[16, false]`   for `J$.C(16, ...) ? ... : J$._()` (generated by &&)
 * e.g. `[16, true]`    for `J$.C(16, ...) ? J$._() : ...`  (generated by ||)
 * @param ast
 */
function computeLazyBooleanLocations(ast) {
    function isJalangiConditionReuse(node) {
        return node.type === 'CallExpression' &&
            node.callee.type === 'MemberExpression' &&
            node.callee.object.type === 'Identifier' &&
            node.callee.object.name === astUtil.JALANGI_VAR &&
            node.callee.property.type === 'Identifier' &&
            node.callee.property.name === '_';
    }

    var lazyBooleanLocations = [];
    var visitorLazyBooleanLocationsPre = {
        "ConditionalExpression": function (node) {

            var potentialJalangiConditional = node.test;
            var isTestJalangiConditional = isJalangiCall(potentialJalangiConditional, 'C');
            var consequentIsJalangiConditionReuse = isJalangiConditionReuse(node.consequent);
            var alternateIsJalangiConditionReuse = isJalangiConditionReuse(node.alternate);
            if (isTestJalangiConditional && (consequentIsJalangiConditionReuse || alternateIsJalangiConditionReuse)) {
                // We have something of the form:
                // - J$.C(IID, ...) ? ... : J$._();
                // - J$.C(IID, ...) ? J$._(): ...;
                lazyBooleanLocations.push(
                    [getIIDOfJalangiCall(potentialJalangiConditional), consequentIsJalangiConditionReuse]
                );
            }
        }
    };
    transformAst(ast, undefined, visitorLazyBooleanLocationsPre, astUtil.CONTEXT.RHS);
    return lazyBooleanLocations;
}

/**
 * given an instrumented AST, returns an array of IIDs dynamic property delete name values, like:
 * `delete o[p]`
 * @param ast
 */
function computeDynamicPropertyDeleteNames(ast) {
    var dynamicPropertyReferenceLocations = [];
    // J$.B(..., 'delete', ..., J$.XXX(iid));

    var visitorDynamicPropertyDeleteNamesPre = {
        "CallExpression": function (node) {
            if (isIndirectJalangiCall(node)) {
                return; // avoid double registration
            }
            var isJalangiBinaryDelete = isJalangiCall(node, 'B');
            if (isJalangiBinaryDelete) {
                var binaryArgument1 = getArgumentsToJalangiCall(node)[1];
                isJalangiBinaryDelete = binaryArgument1.type === 'Literal' && binaryArgument1.value === 'delete';
            }
            if (isJalangiBinaryDelete) {
//                    console.log("Adding location for node with iid: %s", getIIDOfJalangiCall(node));
                var potentialDynamicArgument = unwrapJalangiIgnoreAndAssignCall(getArgumentsToJalangiCall(node)[isJalangiBinaryDelete ? 3 : 2]);
                if (isJalangiCall(potentialDynamicArgument)) {
                    dynamicPropertyReferenceLocations.push(getIIDOfJalangiCall(potentialDynamicArgument))
                }
            }
        }
    };
    transformAst(ast, undefined, visitorDynamicPropertyDeleteNamesPre, astUtil.CONTEXT.RHS);
    return dynamicPropertyReferenceLocations;
}

/**
 * given an instrumented AST, returns an array of pairs of IIDS and number of parameters of the enclosing function
 * e.g. `[[18, 3]]`   for `function(..., ..., ...){...; J$.Fe(18, ...); ...;}`
 * @param ast
 */
function computeParameterCounts(ast) {
    var functionEntryParameterCounts = [];
    var parameterCountStack = [];
    var functionEntryParameterCountsVisitor = {
        "CallExpression": function (node) {
            // simple version: variable update
            var isJalangiFunctionEntry = isJalangiCall(node, "Fe");
            if (isJalangiFunctionEntry) {
                functionEntryParameterCounts.push([getIIDOfJalangiCall(node), parameterCountStack.pop()]);
            }
        },
        "FunctionExpression": function (node) {
            parameterCountStack.push(node.params.length);
        },
        "FunctionDeclaration": function (node) {
            parameterCountStack.push(node.params.length);
        }
    };
    transformAst(ast, undefined, functionEntryParameterCountsVisitor, astUtil.CONTEXT.RHS);
    return functionEntryParameterCounts;
}

/**
 * given an instrumented AST, returns an array of IIDs for the locatios of voided expressions
 * e.g. `[97]`   for `void J$.XXX(97, ...)`
 * @param ast
 */
function computeVoidedExpressions(ast) {
    var voided = [];
    var voidedVisitorPre = {
        "UnaryExpression": function (node) {
            if (node.operator === 'void') {
                var potentialJalangiCall = unwrapJalangiIgnoreAndAssignCall(node.argument);
                if (isJalangiCall(potentialJalangiCall)) {
                    voided.push(getIIDOfJalangiCall(potentialJalangiCall));
                }
            }
        }
    };

    transformAst(ast, undefined, voidedVisitorPre, astUtil.CONTEXT.RHS);
    return voided;
}

/**
 * given an instrumented AST, returns an array of IIDs for the locatios where the for-in variable is updated at the beginning of the loop.
 * e.g. `[97]`   for `for(var p in ...){ var p = J$.X1(.., J$.W(97, ...)) ... }`
 * e.g. `[97]`   for `for(p in ...){ J$.X1(.., p = J$.W(97, ...)) ... }`
 * e.g. `[97]`   for `for(o.p in ...){ J$.X1(.., J$.P(97, ...)) ... }`
 * @param ast
 */
function computeForInVariableUpdates(ast) {
    var updates = [];

    var updatesVisitorPre = {
        "ForInStatement": function (node) {
            var firstStatement = node.body.body[0];
            var writeCall;

            if (firstStatement.type === "VariableDeclaration") {
                // for(var x in ...){}
                // =>
                // var x = J$.X1(.., J$.W(iid, ))
                writeCall = getArgumentsToJalangiCall(firstStatement.declarations[0].init)[1];
            } else {
                var unboxed = getArgumentsToJalangiCall(firstStatement.expression)[1];
                if (unboxed.type === "CallExpression") {
                    // for(o.p in ...){}
                    // =>
                    // J$.X1(.., J$.P(iid, ))
                    writeCall = unboxed;
                } else {
                    // var x; for(x in ...){}
                    // =>
                    // J$.X1(.., x = J$.W(iid, ))
                    writeCall = unboxed.right;
                }
            }

            updates.push(getIIDOfJalangiCall(writeCall));
        }
    };

    transformAst(ast, undefined, updatesVisitorPre, astUtil.CONTEXT.RHS);
    return updates;
}

/**
 * given an instrumented AST, returns an array of IIDs for the locatios of global variable declarations
 * e.g. `[97]`   for `J$.N(97, ...) ... function(){ ... J$.N(42, ...) ... }`
 * @param ast
 */
function computeGlobalVariableDeclarations(ast) {
    var globalVariableDeclarations = [];
    var functionLevel = 0;
    var globalVariableDeclarationsVisitorPre = {
        "CallExpression": function (node) {
            var isDeclaration = isJalangiCall(node, "N");
            if (isDeclaration && functionLevel === 0) {
                globalVariableDeclarations.push(getIIDOfJalangiCall(node));
            }
        },
        "FunctionExpression": function (node) {
            functionLevel++;
        },
        "FunctionDeclaration": function (node) {
            functionLevel++;
        }
    };
    var globalVariableDeclarationsVisitorPost = {
        "FunctionExpression": function (node) {
            functionLevel--;
            return node;
        },
        "FunctionDeclaration": function (node) {
            functionLevel--;
            return node;
        }
    };
    transformAst(ast, globalVariableDeclarationsVisitorPost, globalVariableDeclarationsVisitorPre, astUtil.CONTEXT.RHS);
    return globalVariableDeclarations;
}

/**
 * given an instrumented AST, returns an array of IIDs for the locatios of function declarations
 * e.g. `[97]`   for `J$.N(97, 'f', J$.T(..., f, ...))`
 * @param ast
 */
function computeFunctionDeclarations(ast) {
    var functionDeclarations = [];
    var functionDeclarationsVisitorPre = {
        "CallExpression": function (node) {
            if(isJalangiCall(node, "N")) {
                var potentialFunctionLiteral = getArgumentsToJalangiCall(node)[2];
                if (isJalangiCall(potentialFunctionLiteral, "T")) {
                    functionDeclarations.push(getIIDOfJalangiCall(node));
                }
            }
        }
    };
    transformAst(ast, undefined, functionDeclarationsVisitorPre, astUtil.CONTEXT.RHS);
    return functionDeclarations;
}

// handle node.js and browser
var exportObj;
if (typeof exports === 'undefined') {
    exportObj = {};
    if (typeof window !== 'undefined') {
        window.astUtil = exportObj;
    }
} else {
    exportObj = exports;
}

// TODO merge these queries to only do a single AST traversal...
exportObj.computeLazyBooleanLocations = computeLazyBooleanLocations;
exportObj.computeDynamicPropertyDeleteNames = computeDynamicPropertyDeleteNames;
exportObj.computeParameterCounts = computeParameterCounts;
exportObj.computeVoidedExpressions = computeVoidedExpressions;
exportObj.computeGlobalVariableDeclarations = computeGlobalVariableDeclarations;
exportObj.computeFunctionDeclarations = computeFunctionDeclarations;
exportObj.computeForInVariableUpdates = computeForInVariableUpdates;