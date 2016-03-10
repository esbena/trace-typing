///<reference path="../src/types.d.ts"/>

import * as assert from "./assert-async-mocha";
import * as path from "path";
import * as fs from "fs";
import * as util from 'util';

import * as PersistentResults from "../src/PersistentResults"
import * as Misc from "../src/Misc"
import * as State from "../src/trace-replaying/State"
import * as TraceImporter from "../src/TraceImporter"
import * as TraceMaker from "../src/TraceMaker";
import * as TypeInferencer from "../src/typing/TypeInferencer";
import * as TypeLattices from "../src/typing/TypeLattices";
import * as TypeChecker from "../src/typing/TypeChecker";
import * as TypeImpls from "../src/typing/TypeImpls";
import MetaInformationExplainerImpl from "../src/MetaInformationExplainer";
import * as VariableManager from "../src/VariableManager";
import * as TraceReplayer from "../src/trace-replaying/TraceReplayer";
import * as TypedTraceReplayer from "../src/trace-replaying/TypedTraceReplayer";
import * as maker from "../src/TraceMaker";
import * as TypeCheckerTester from './TypeCheckerTester';
import * as ConfigLoader from "../src/ConfigLoader";
import * as TestUtil from "./TestUtil";

function countUniqueIIDs(messages:IIDRelatedMessage[]) {
    var seen = new Set<string>();
    messages.forEach((m:IIDRelatedMessage) => {
        seen.add(m.iid);
    });
    return seen.size;
}
function countUniqueFunctionIIDs(messages:IIDRelatedMessage[]) {
    var seen = new Set<string>();
    messages.forEach((m:IIDRelatedMessage) => {
        seen.add(m.functionIID);
    });
    return seen.size;
}

var showLocation = true;

function isPartOfTestedApplication(iid:string, filterToBenchmarkCodeOnly:boolean, explainer:MetaInformationExplainer) {
    if (filterToBenchmarkCodeOnly) {
        // we are testing application Y in X/node_modules/Y, it is run from X/main.js
        var location = explainer.getIIDSourceLocation(iid).file;
        var isDependencyOfApplication = /(\/node_modules\/.*\/node_modules\/)/.test(location);
        var isMainFile = !/(\/node_modules\/)/.test(location);
        return !isDependencyOfApplication && !isMainFile;
    }
    return true;
}

function getVisitedLines(visitedIIDs:Set<string>, filterToBenchmarkCodeOnly:boolean, explainer:MetaInformationExplainer):Set<string> {
    var visitedLines = new Set<string>();
    visitedIIDs.forEach(iid => {
        if (isPartOfTestedApplication(iid, filterToBenchmarkCodeOnly, explainer)) {
            var location = explainer.getIIDSourceLocation(iid);
            visitedLines.add(util.format("%s:%s", location.file, location.beginLine));
            visitedLines.add(util.format("%s:%s", location.file, location.endLine));
        }
    });
    return visitedLines;
}
function getVisitedFiles(visitedIIDs:Set<string>, filterToBenchmarkCodeOnly:boolean, explainer:MetaInformationExplainer):Set<string> {
    var visitedFiles = new Set<string>();
    visitedIIDs.forEach(iid => {
        if (isPartOfTestedApplication(iid, filterToBenchmarkCodeOnly, explainer)) {
            var location = explainer.getIIDSourceLocation(iid);
            visitedFiles.add(location.file);
        }
    });
    visitedFiles.delete("");
    visitedFiles.delete(undefined);
    return visitedFiles;
}
export function testTrace(err:any, trace:Trace, expectedErrorCount:number, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig, filterToBenchmarkCodeOnly = false, typeSystemDescription?:string, enableSJSChecks:boolean = false) {
    if (err) {
        done(err);
        throw err;
    }
    var explainer = new MetaInformationExplainerImpl(trace.iidMap);


    function messageLocationComparator(m1:IIDRelatedMessage, m2:IIDRelatedMessage) {
        var l1 = explainer.getIIDSourceLocation(m1.iid);
        var l2 = explainer.getIIDSourceLocation(m2.iid);

        var fileCmp = l1.file.localeCompare(l2.file);
        if (fileCmp !== 0) {
            return fileCmp;
        }
        var lineCmp = l1.beginLine - l2.beginLine;
        if (lineCmp !== 0) {
            return lineCmp;
        }

        var columnCmp = l1.beginColumn - l2.beginColumn;
        if (columnCmp !== 0) {
            return columnCmp;
        }
        return 0;
    }

    function locationString(e:IIDRelatedMessage) {
        return showLocation ? explainer.getIIDSourceLocation(e.iid) + ": " : ""
    }

    function isInterestingFile(fileName:string) {
        return true;
    }

    try {
        // TODO refactor some of this to separate file
        console.log("Trace replay...");
        var traceReplayResults = TraceReplayer.replayTrace(trace);
        var visitedBenchmarkLines = getVisitedLines(traceReplayResults.visitedIIDs, filterToBenchmarkCodeOnly, explainer);
        var visitedLines = getVisitedLines(traceReplayResults.visitedIIDs, false, explainer);
        var visitedBenchmarkFiles = getVisitedFiles(traceReplayResults.visitedIIDs, filterToBenchmarkCodeOnly, explainer);
        var visitedFiles = getVisitedFiles(traceReplayResults.visitedIIDs, false, explainer);
        console.log("Done replaying %d statements (benchmark: %d lines, %d files) (all: %d lines, %d files)", trace.statements.length, visitedBenchmarkLines.size, visitedBenchmarkFiles.size, visitedLines.size, visitedFiles.size);
        console.log("Benchmark files: ");
        visitedBenchmarkFiles.forEach(f => console.log("\t%s", f));
        console.log("All files: ");
        visitedFiles.forEach(f => console.log("\t%s", f));

        //Misc.toArray(traceReplayResults.visitedLines).sort().forEach(l => console.log(l));
        var visitedLinesOnly = false;
        if (visitedLinesOnly) {
            done();
            return;
        }
        var typeLatticePair = inferencerConfig();

        var results = TypedTraceReplayer.replayTrace(traceReplayResults.variableValues, traceReplayResults.variableList, trace.statements, flowConfig, typeLatticePair, explainer);
        console.log("Type checking...");
        var enabledConstraints:TypeChecker.ConstraintKinds[] = [];
        var messages:TypeChecker.IIDRelatedConstaintFailureMessage[] = TypeChecker.check(trace.statements, results.propagatedEnv, results.inferredEnv, typeLatticePair.types, new MetaInformationExplainerImpl(trace.iidMap), enabledConstraints, enableSJSChecks);
        messages = messages.filter(m => {
            return isPartOfTestedApplication(m.iid, filterToBenchmarkCodeOnly, explainer);
        });
        messages.sort(messageLocationComparator);
        var iidErrors = messages.filter(m => m.type === 'error');
        var iidWarnings = messages.filter(m => m.type === 'warning');

        var dynamicErrorCount = iidErrors.length;

        var result:TypeChecksResult = {kind: PersistentResults.ExperimentResultKinds.TypeChecksResult, data: {}};
        for (var k in TypeChecker.ConstraintKinds) {
            if (!isNaN(parseInt(k))) {
                var relevantMessages = iidErrors/*ignoring warnings!*/.filter(m => m.constraintKind === parseInt(k));
                var dynamicMessageCount = relevantMessages.length;
                var staticMessageCount = countUniqueIIDs(relevantMessages);
                var staticFunctionMessageCount = countUniqueFunctionIIDs(relevantMessages);
                result.data[k] = {
                    Dynamic: dynamicMessageCount,
                    Static: staticMessageCount,
                    StaticFunctions: staticFunctionMessageCount
                }
            }
        }
        console.log("Output...");
        var annotated = PersistentResults.annotate([result], trace.sources, typeSystemDescription);
        var successfulTest = expectedErrorCount === -1 || (expectedErrorCount === dynamicErrorCount);

        function innerDone() {
            if (expectedErrorCount !== -1) {
                assert.equal(dynamicErrorCount, expectedErrorCount, done);
                return;
            }
            done();
        }

        PersistentResults.save(annotated, function () {
            if (true || expectedErrorCount !== -1) {
                var show = expectedErrorCount !== dynamicErrorCount;
                if (dynamicErrorCount > 0 && show) {
                    var showErrorsAndWarnings = false;
                    if (showErrorsAndWarnings) {
                        var fileErrorCountOrder:string[] = [];
                        var fileErrorCounts = new Map<string, number>();
                        iidErrors.forEach(e => {
                            var key = explainer.getIIDSourceLocation(e.iid).file;
                            if (!fileErrorCounts.has(key)) {
                                fileErrorCounts.set(key, 0);
                                fileErrorCountOrder.push(key);
                            }
                            fileErrorCounts.set(key, fileErrorCounts.get(key) + 1);
                        });
                        fileErrorCountOrder.sort((f1, f2) => -1 * (fileErrorCounts.get(f1) - fileErrorCounts.get(f2)));
                        fileErrorCountOrder.forEach(file => {
                            console.log("%d errors in %s", fileErrorCounts.get(file), file);
                        });
                        iidErrors.forEach(e => isInterestingFile(locationString(e)) ? console.log("%sError (kind:%s): %s", locationString(e), TypeChecker.ConstraintKinds[e.constraintKind], e.message) : undefined);
                        iidWarnings.forEach(e => console.log("%sWarning (kind:%s): %s", locationString(e), TypeChecker.ConstraintKinds[e.constraintKind], e.message));
                    }
                    var sourceLocationErrors:SourceRelatedMessage[] = iidErrors.map(e => {
                        return {
                            sourceLocation: explainer.getIIDSourceLocation(e.iid),
                            message: e.message,
                            type: e.type
                        };
                    });
                    var showInBrowser = false;
                    sourceLocationErrors = sourceLocationErrors.filter(e => isInterestingFile(e.sourceLocation.file));
                    if (showInBrowser && sourceLocationErrors.length > 0) {
                        explainer.displayMessagesInBrowser("Typechecking with configuration: " + typeSystemDescription, sourceLocationErrors, innerDone);
                    } else {
                        innerDone();
                    }
                } else {
                    innerDone();
                }
            } else {
                innerDone();
            }
        });
    } catch (e) {
        done(e);
        throw e;
    }
}
