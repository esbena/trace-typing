///<reference path="../src/types.d.ts"/>


import * as assert from "./assert-async-mocha";
import * as path from "path";
import * as fs from "fs";
import * as util from 'util';
import * as mkdirp from 'mkdirp';

import * as PersistentResults from "../src/PersistentResults"
import * as Misc from "../src/Misc"
import * as State from "../src/trace-replaying/State"
import * as TraceImporter from "../src/TraceImporter"
import * as TraceMaker from "../src/TraceMaker";
import * as TypeInferencer from "../src/typing/TypeInferencer";
import * as TypeLattices from "../src/typing/TypeLattices";
import * as TypeChecker from "../src/typing/TypeChecker";
import * as TypeImpls from "../src/typing/TypeImpls";
import MetaInformationExplainerImpl from "../src/MetaInformationExplainer"; import * as VariableManager from "../src/VariableManager";
import * as TraceReplayer from "../src/trace-replaying/TraceReplayer";
import * as TypedTraceReplayer from "../src/trace-replaying/TypedTraceReplayer";
import * as maker from "../src/TraceMaker";
import * as TypeCheckerTester from './TypeCheckerTester';
import * as ConfigLoader from "../src/ConfigLoader";
import * as TestUtil from "./TestUtil";


var inferenceConfigs = (function () {
    return {
        fullIntersection: TypeLattices.makeFullIntersection,
        simpleSubtyping: TypeLattices.makeSimpleSubtyping,
        simpleSubtypingWithUnion: TypeLattices.makeSimpleSubtypingWithUnion,
        SJS: TypeLattices.makeSJS
    };
})();

var stringIdentityCache = new Map<string, Object>();
function getIdentity<T>(o:T) {
    var key = JSON.stringify(o);
    if (!stringIdentityCache.has(key)) {
        stringIdentityCache.set(key, o);
    }
    return <T> stringIdentityCache.get(key);
}
class NamedVariableRead {

    constructor(public name:string, public sink:Variable) {
        return getIdentity(this);
    }
}
class SuccessiveRead {
    constructor(public first:NamedVariableRead, public second:NamedVariableRead) {
        return getIdentity(this);
    }
}
class RefinedRead {
    constructor(public guard:NamedVariableRead, public refined:NamedVariableRead) {
        return getIdentity(this);
    }
}
class SuccessiveReadsFinderVisitor implements TraceStatementVisitor<void> {
    private activeReads = new Map<Variable, Set<NamedVariableRead>>();
    public successiveReads = new Set<SuccessiveRead>();
    private noop = function () {
    };
    private currentSink:Variable = undefined;
    private expressionVisitor = {
        visitRead: (e:Read) => {
            var v = e.source;
            if (v.named && v.name !== 'this' /* ignore the this-variable, it makes a lot of noise in the results */) {
                var namedVariableRead = new NamedVariableRead(v.name, this.currentSink);
                var r = this.activeReads;
                if (!r.has(v)) {
                    r.set(v, new Set());
                }
                r.get(v).forEach(pre => {
                    this.successiveReads.add(new SuccessiveRead(pre, namedVariableRead));
                });
                r.get(v).add(namedVariableRead);
            }
        },
        visitFieldRead: this.noop,
        visitNew: this.noop,
        visitPrimitiveExpression: this.noop
    };

    visitWrite(e:Write) {
        if (e.sink.named) {
            this.activeReads.delete(e.sink);
        } else {
            this.currentSink = e.sink;
            e.rhs.applyExpressionVisitor(this.expressionVisitor);
        }
    }

    visitFieldWrite(e:FieldWrite) {
    }

    visitDelete(e:Delete) {

    }

    visitInfo(e:Info) {

    }
}
function getSuccessiveReads(trace:Trace):Set<SuccessiveRead> {
    var visitor = new SuccessiveReadsFinderVisitor();
    trace.statements.forEach(statement => {
        statement.applyStatementVisitor(visitor);
    });
    return visitor.successiveReads;
}
function getRefinedReads(successiveReads:Set<SuccessiveRead>, abstractEnv:Variables<TupleType>, lattice:CompleteLattice<TupleType>, explainer:MetaInformationExplainer):Set<RefinedRead> {
    var refined = new Set<RefinedRead>();
    var undef = TypeImpls.convenienceConstants.UndefinedTop;
    var nullType = TypeImpls.convenienceConstants.NullTop;
    successiveReads.forEach(r => {
        var t1 = abstractEnv.read(r.first.sink);
        var t2 = abstractEnv.read(r.second.sink);

        // do not let top-object influence results
        if (TypeImpls.TupleAccess.isObject(t1) && TypeImpls.isObjectTypeEqual(TypeImpls.TupleAccess.getObject(t1), TypeImpls.constants.ObjectTop)) {
            return;
        }
        if (TypeImpls.TupleAccess.isObject(t2) && TypeImpls.isObjectTypeEqual(TypeImpls.TupleAccess.getObject(t2), TypeImpls.constants.ObjectTop)) {
            return;
        }
        // ignore objects that are very similar (likely due to optional properties)
        if (TypeImpls.TupleAccess.isObject(t1) && TypeImpls.TupleAccess.isObject(t2) && isEqualish(TypeImpls.TupleAccess.getObject(t1), TypeImpls.TupleAccess.getObject(t2))) {
            return;
        }

        // do not let undefined influence the results
        if (TypeImpls.isTupleTypeEqual(t1, undef) || TypeImpls.isTupleTypeEqual(t2, undef)) {
            return;
        }
        if (TypeImpls.isTupleTypeEqual(t1, nullType) || TypeImpls.isTupleTypeEqual(t2, nullType)) {
            return;
        }

        // do not let undefinedness-differences influence the results
        t1 = lattice.lub(t1, undef);
        t2 = lattice.lub(t2, undef);
        t1 = lattice.lub(t1, nullType);
        t2 = lattice.lub(t2, nullType);

        var isRefined = !TypeImpls.isTupleTypeEqual(t1, t2);
        var debug = true;
        if (debug && isRefined && isLine(r.first, 5089, explainer)) {
            console.log("Checking refinement for:\n\t%s\n\t%s\n\t=>\n\t%s\n\t%s\n\t=>\n\t%s",
                JSON.stringify(r.first),
                JSON.stringify(r.second),
                TypeImpls.toPrettyString(t1),
                TypeImpls.toPrettyString(t2),
                isRefined
            );
        }
        if (isRefined) {
            refined.add(new RefinedRead(r.first, r.second));
        }
    });
    return refined;
}
function isEqualish(o1:ObjectType, o2:ObjectType) {
    var p1s = new Set<string>();
    var p2s = new Set<string>();
    var ps = new Set<string>();
    Object.keys(o1.properties).forEach(p => (ps.add(p), p1s.add(p)));
    Object.keys(o2.properties).forEach(p => (ps.add(p), p2s.add(p)));
    var notInBoth = new Set<string>();
    ps.forEach(p => {
        if (!p1s.has(p) || !p2s.has(p)) {
            notInBoth.add(p);
        }
    });
    if(0 < notInBoth.size && notInBoth.size < 5 && ps.size > 15) {
        return true;
    }
    return false;
}
function isLine(read:NamedVariableRead, line:number, explainer:MetaInformationExplainer) {
    return explainer.getIIDSourceLocation(read.sink.iid).beginLine === line;
}
function getTypeGuards(refinedReads:Set<RefinedRead>):Set<Read> {
    var mapped = new Set();
    refinedReads.forEach(r => mapped.add(r.guard));
    return mapped;
}
function getNamesOfRefinedVariables(refinedReads:Set<RefinedRead>):Set<string> {
    var mapped = new Set<string>();
    refinedReads.forEach(r => mapped.add(r.guard.name));
    return mapped;
}


/**
 * Creates the simple abstract environment: merges (named) variables context insensitively.
 */
function makeAbstractEnv(origExpressionEnv:Variables<TupleType>, variablesList:Variable[], lattice:CompleteLattice<TupleType>):Variables<TupleType> {
    function makeVariableContextInsensitive(variable:Variable):Variable {
        return VariableManager.canonicalize({
            named: false,
            iid: variable.iid,
            functionIID: variable.functionIID
        });
    }

    var variables = new State.VariablesImpl<TupleType>();
    variablesList.forEach(v => {
        if (!v.named) {
            var av = makeVariableContextInsensitive(v);
            var pre:TupleType = variables.read(av, true);
            if (pre === undefined) {
                pre = TypeImpls.constants.Bottom;
            }
            variables.write(av, lattice.lub(pre, origExpressionEnv.read(v)));
        }
    });

    return {
        read: function (variable:Variable):TupleType {
            if (variable.named) {
                throw new Error("Should not ask for named variables (due to implementation issues)");
            }
            return variables.read(makeVariableContextInsensitive(variable));
        },
        write: undefined
    }
}
function sortRefinedReadsByLineAndGuardName(refinedReads:Set<RefinedRead>, explainer:MetaInformationExplainer):RefinedRead[] {
    var sortedRefinedReads:RefinedRead[] = [];
    refinedReads.forEach(r => sortedRefinedReads.push(r));
    sortedRefinedReads.sort((e1, e2) => {
        var loc1:SourceLocation = explainer.getIIDSourceLocation(e1.guard.sink.iid);
        var loc2:SourceLocation = explainer.getIIDSourceLocation(e2.guard.sink.iid);
        var lineCmp = loc1.beginLine - loc2.beginLine;
        if (lineCmp !== 0) {
            return lineCmp;
        }
        return e1.guard.name.localeCompare(e2.guard.name);
    });
    return sortedRefinedReads;
}
function prettyPrintLocationsOfTypeGuards(refinedReads:Set<RefinedRead>, explainer:MetaInformationExplainer) {
    console.log("Type guards: ");
    var sortedRefinedReads = sortRefinedReadsByLineAndGuardName(refinedReads, explainer);
    var lines:string[] = [];
    sortedRefinedReads.forEach(r => {
        var guardLoc = explainer.getIIDSourceLocation(r.guard.sink.iid);
        lines.push(util.format("%d: %s", guardLoc.beginLine, r.guard.name));
    });

    var seenLines = new Set<string>();
    lines.forEach(l => {
        if (seenLines.has(l)) {
            return;
        }
        seenLines.add(l);
        console.log("\t%s", l);
    });
}
function dumpTypeGuardLines(refinedReads:Set<RefinedRead>, explainer:MetaInformationExplainer) {
    var dir = "out/type-guard-lines";
    mkdirp.sync(dir);

    var groupedByFile = new Map<string, Set<RefinedRead>>();

    refinedReads.forEach(r => {
        var guardLoc = explainer.getIIDSourceLocation(r.guard.sink.iid);
        var key = guardLoc.file;
        if (!groupedByFile.has(key)) {
            groupedByFile.set(key, new Set());
        }
        groupedByFile.get(key).add(r);
    });

    groupedByFile.forEach((refinedReads:Set<RefinedRead>, file:string)=> {
        var encoding = "utf8";
        var fileContent = fs.readFileSync(file, encoding);
        var fileLines = fileContent.split('\n');

        function readLine(line:number) {
            return fileLines[line - 1];
        }

        var lines:string[] = [];
        refinedReads.forEach((r => {
            var guardLoc:SourceLocation = explainer.getIIDSourceLocation(r.guard.sink.iid);
            lines.push(util.format("%s:%d %s", path.relative(process.cwd(), guardLoc.file), guardLoc.beginLine, readLine(guardLoc.beginLine)));
        }));

        var hash = require('crypto').createHash('md5').update(fileContent).digest("hex");
        var outfile = util.format("%s/%s@%s.txt", dir, path.basename(file), hash);
        var uniqueLines:string[] = [];
        if (fs.existsSync(outfile)) {
            lines = lines.concat(fs.readFileSync(outfile, encoding).split("\n"));
        }

        var seenLines = new Set<string>();
        lines.forEach(l => {
            l = l.trim();
            if (seenLines.has(l)) {
                return;
            }
            seenLines.add(l);
            uniqueLines.push(l);
        });
        uniqueLines.sort((l1:string, l2:string) => {
            return (+l1.split(" ")[0]) - (+l2.split(" ")[0])
        });
        var outcontent = uniqueLines.join("\n");
        fs.writeFileSync(outfile, outcontent, encoding);
        // console.log(outfile);
        console.log("%s\n", fs.readFileSync(outfile, encoding));
    });
}
export function testTrace(err:any, trace:Trace, expectedVariables:Set<string>, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    stringIdentityCache.clear();
    if (err) {
        done(err);
        throw err;
    }
    var explainer = new MetaInformationExplainerImpl(trace.iidMap);

    try {
        // TODO refactor some of this to separate file
        // console.log("Trace replay...");
        console.log("Replaying...");
        var traceReplayResults = TraceReplayer.replayTrace(trace);
        var typeLatticePair = inferencerConfig();

        var results = TypedTraceReplayer.replayTrace(traceReplayResults.variableValues, traceReplayResults.variableList, trace.statements, flowConfig, typeLatticePair, explainer);

        console.log("Finding successiveReads ...");

        var successiveReads = getSuccessiveReads(trace);

        console.log("|successiveReads|: %d", successiveReads.size);

        var abstractEnv = makeAbstractEnv(results.inferredEnv, traceReplayResults.variableList, typeLatticePair.types);

        console.log("Finding refinedReads ...");

        var refinedReads:Set<RefinedRead> = getRefinedReads(successiveReads, abstractEnv, typeLatticePair.types, explainer);

        console.log("|refinedReads|: %d", refinedReads.size);

        var namesOfRefinedVariables = getNamesOfRefinedVariables(refinedReads);

        console.log("Outputting ...");

        //prettyPrintLocationsOfTypeGuards(refinedReads, explainer);
        dumpTypeGuardLines(refinedReads, explainer);
        if (expectedVariables !== undefined) {
            assert.assert(Misc.isSetFlatEqual(namesOfRefinedVariables, expectedVariables), done);
        } else {
            done();
        }
    } catch (e) {
        done(e);
        throw e;
    }
}

function testFile(file:string, expectedVariables:string[], inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    var set: Set<string>;
    if (expectedVariables !== undefined) {
        set = new Set();
        expectedVariables.forEach(v => set.add(v));
    }
    TraceMaker.getTraceFromSourceFile(file, function (err:any, trace:Trace) {
        testTrace(err, trace, set, inferencerConfig, done, flowConfig);
    });
}
function testSource(source:string, expectedVariables:string[], inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    var set = new Set();
    expectedVariables.forEach(v => set.add(v));
    TraceMaker.getTraceFromSource(source, function (err:any, trace:Trace) {
        testTrace(err, trace, set, inferencerConfig, done, flowConfig);
    });
}

if(typeof describe !== 'undefined') {
    describe.only("Variable refinement unit tests", function () {
        var config = inferenceConfigs.simpleSubtypingWithUnion;
        this.timeout(5 * 1000);
        describe("Guard name identification", function () {
            it('Should work for canonical example', function (done) {
                testSource("function f(x){if(typeof x === 'boolean'){x;}} f(true); f(42);", ['x'], config, done, {});
            });
            it('Should work for note example', function (done) {
                testSource("function f(x){var y = x === true? 42: 87; if(y === 42){return;} x;} f(true); f(42);", ['x'], config, done, {});
            });
            it('Should work for multiple variables', function (done) {
                testSource("function f(x){if(typeof x === 'boolean'){x;}} f(true); f(42);" +
                    "function g(y){if(typeof y === 'boolean'){y;}} g(true); g(42);", ['x', 'y'], config, done, {});
            });
            it('Should work for underscore', function (done) {
                this.timeout(60 * 1000);
                testFile("fixtures/underscore-singlefile.js", undefined, config, done, {});
            });
        });
        describe.skip("Benchmarks refinements", function () {
            this.timeout(5 * 60 * 1000);
            TestUtil.getBenchmarkTraceFiles().forEach(file => {
                it("Should work for " + path.basename(file), function (done) {
                    var traceImporter:TraceImporter.TraceImporter = new TraceImporter.TraceImporter();
                    traceImporter.import(file, function (err:any, imported:TraceImport) {
                        if (err) {
                            done(err);
                            return;
                        }
                        testTrace(err, imported.trace, undefined, config, done, {});
                    });
                });
            });
        });
    });
}