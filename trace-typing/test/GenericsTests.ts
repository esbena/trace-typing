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
import * as GenericFunctionTypeInferencer from "../src/typing/GenericFunctionTypeInferencer";
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

type GenericFunctionTypeString = String;

class GenericFunction {
    static cache:Map<string /* pattern@iid */, GenericFunction>;

    constructor(private pattern:GenericFunctionTypeString, public typeParameterLubs:Map<string, TupleType>, public typeparameterUsageCount:number, public iid:string) {
        var key:string = GenericFunction.makeCacheKey(this);
        if (!GenericFunction.cache.has(key)) {
            GenericFunction.cache.set(key, this);
        }
        return GenericFunction.cache.get(key);
    }

    private static makeCacheKey(instance:GenericFunction):string {
        return instance.pattern + "@" + instance.iid;
    }

    toString() {
        var instantiations: string[] = [];
        this.typeParameterLubs.forEach((instantiation, name) => {
           instantiations.push(util.format("%s as %s", name, TypeImpls.toPrettyString(instantiation)));
        });
        return util.format("%s with %s", this.pattern, instantiations.join(", "));
    }
}
function dumpGenericTypes(functions:GenericFunction[], explainer:MetaInformationExplainer) {
    var maxTypeParameterUsageCount = Math.max.apply(undefined, functions.map(f => f.typeparameterUsageCount));
    for (var i = 1; i <= maxTypeParameterUsageCount; i++) {
        console.log("Type parameter usage count = %d: ", i);
        functions.filter(f => f.typeparameterUsageCount === i).forEach(f => {
            var location = explainer.getIIDSourceLocation(f.iid);
            console.log("\t%s: %s\n", location.isPseudo ? 'native' : location.toString(), f.toString());
        });
    }
}

function typeparameterLub(f:SingleFunctionType, fs:SingleFunctionType[], lattice: CompleteLattice<TupleType>):Map<string, TupleType> {
    var typeParameterInstantiations = new Map<string, Set<TupleType>>();

    function register(key:string, instantiations:Set<TupleType>) {
        if (!typeParameterInstantiations.has(key)) {
            typeParameterInstantiations.set(key, new Set<TupleType>());
        }
        instantiations.forEach(instantiation =>
            typeParameterInstantiations.set(key, typeParameterInstantiations.get(key).add(instantiation))
        );
    }

    function registerMaybe(type:TupleType, instantiations:Set<TupleType>) {
        if (TypeImpls.TupleAccess.isTypeParameter(type)) {
            register(TypeImpls.TupleAccess.getTypeParameter(type).name, instantiations);
        }
    }

    var topLevelTypes:[TupleType, Set<TupleType>][] = [];
    topLevelTypes.push([f.base, Misc.toSet(fs.map(f => f.base))]);
    topLevelTypes.push([f.result, Misc.toSet(fs.map(f => f.result))]);
    for (var i = 0; i < f.args.length; i++) {
        topLevelTypes.push([f.args[i], Misc.toSet(fs.map(f => f.args[i]))]);
    }
    var propertyTypes:[TupleType, Set<TupleType>][] = Array.prototype.concat.apply([], topLevelTypes.
        filter(t => TypeImpls.TupleAccess.isObject(t[0])).
        map(t => TypeImpls.TupleAccess.getObject(t[0])).
        map((o:ObjectType):[TupleType, Set<TupleType>][] => {
            var names = Object.keys(o.properties);
            return names.map(n => <[TupleType, Set<TupleType>]>[o.properties[n], Misc.toSet([TypeImpls.constants.Bottom])] /* XXX not inferring instantiations if instantiations only occur in properties ... */);
        })
    );

    var types:[TupleType, Set<TupleType>][] = [];
    types = types.concat(topLevelTypes);
    types = types.concat(propertyTypes);
    types.forEach(t => registerMaybe(t[0], t[1]));

    var lubMap = new Map<string, TupleType>();
    typeParameterInstantiations.forEach((instantiations, k) => {
        var lubbed = Misc.toArray(instantiations).reduce((t1: TupleType, t2: TupleType) => lattice.lub(t1, t2), TypeImpls.constants.Bottom);
        lubMap.set(k, lubbed);
    });
    return lubMap;
}
function testTrace(err:any, trace:Trace, expectsGenerics:boolean, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    if (err) {
        done(err);
        throw err;
    }
    var explainer = new MetaInformationExplainerImpl(trace.iidMap);
    GenericFunction.cache = new Map<string, GenericFunction>();

    try {
        var traceReplayResults = TraceReplayer.replayTrace(trace);

        var config = inferencerConfig();

        // extract function types
        var functions = new Map<Instance, Set<SingleFunctionType>>();
        var inferencer:TypeInferencer = new TypeInferencer.TypeInferencerImpl(config.types, config.initialFunctionTypeMaker, config.useSJSAscription);
        traceReplayResults.instances.forEach(instance => {
            instance.functionUsages.forEach(functionUsage => {
                var functionType = inferencer.getAscriber().ascribeFunctionType(functionUsage, [instance.shapes[0].meta.iid]);
                if (!functions.has(instance)) {
                    functions.set(instance, new Set<SingleFunctionType>());
                }
                functions.get(instance).add(functionType);
            });
        });

        // identify potential pattern instantiations
        var genericFunctions = new Set<GenericFunction>();
        var monomorphicFunctionCount = 0;
        var polymorphicFunctionCount = 0;
        var untypableFunctionCount = 0;
        var arityOverloadedFunctionCount = 0;

        function sameArity(fs:SingleFunctionType[]):boolean {
            var representative = fs[0].args.length;
            return fs.every(f => f.args.length === representative);
        }

        functions.forEach((fs, instance) => {
            var isMonomorphic = false;
            var isArityOverloaded = false;
            var isUntypable = false;
            var isPolymorphicTypable = false;

            var representative = Misc.toArray(fs)[0];
            if (Misc.toArray(fs).every(f => TypeImpls.isSingleFunctionTypeEqual(f, representative))) {
                isMonomorphic = true;
            } else {
                var arityOverloaded = !sameArity(Misc.toArray(fs));
                if (arityOverloaded) {
                    isArityOverloaded = true
                }
                var groupedByArity:SingleFunctionType[][] = [];
                fs.forEach(f => {
                    var arity = f.args.length;
                    if (!groupedByArity[arity]) {
                        groupedByArity[arity] = [];
                    }
                    groupedByArity[arity].push(f);
                });
                groupedByArity.forEach(fs => {
                    var genericFunction = GenericFunctionTypeInferencer.substituteInFunctions(fs);
                    if (genericFunction !== undefined) {
                        isPolymorphicTypable = true;
                        genericFunctions.add(new GenericFunction(TypeImpls.functionToPrettyString(genericFunction), typeparameterLub(genericFunction, fs, config.types), GenericFunctionTypeInferencer.typeparameterUsageCount(genericFunction), instance.shapes[0].meta.iid));
                    } else {
                        isUntypable = true;
                    }
                });
            }
            if (isMonomorphic) {
                monomorphicFunctionCount++;
            }
            if (isPolymorphicTypable && !isUntypable) {
                polymorphicFunctionCount++;
            }
            if (isUntypable) {
                untypableFunctionCount++;
                //console.log("untypable:");
                //fs.forEach(f => {
                //    console.log("\t%s", TypeImpls.functionToPrettyString(f));
                //});
            }
            if (isArityOverloaded) {
                arityOverloadedFunctionCount++;
            }
        });

        console.log("monomorphicFunctionCount: %d", monomorphicFunctionCount);
        console.log("polymorphicFunctionCount: %d", polymorphicFunctionCount);
        console.log("untypableFunctionCount: %d", untypableFunctionCount);
        console.log("(arityOverloadedFunctionCount: %d)", arityOverloadedFunctionCount);
        dumpGenericTypes(Misc.toArray(genericFunctions), explainer);
        if (expectsGenerics !== undefined) {
            var hasGenerics = Misc.toArray(genericFunctions).filter(f => 1 < f.typeparameterUsageCount).length > 0;
            assert.equal(hasGenerics, expectsGenerics, done);
        } else {
            done();
        }
    } catch (e) {
        done(e);
        throw e;
    }
}

function testFile(file:string, expectsGenerics:boolean, inferencerConfig:InferencerConfig, done:Function) {
    TraceMaker.getTraceFromSourceFile(file, function (err:any, trace:Trace) {
        testTrace(err, trace, expectsGenerics, inferencerConfig, done, {});
    });
}

function testSource(source:string, expectsGenerics:boolean, inferencerConfig:InferencerConfig, done:Function) {
    TraceMaker.getTraceFromSource(source, function (err:any, trace:Trace) {
        testTrace(err, trace, expectsGenerics, inferencerConfig, done, {});
    });
}

describe("Generics identification", function () {
    var config = inferenceConfigs.simpleSubtypingWithUnion;
    this.timeout(5 * 1000);
    describe("Simple examples", function () {
        describe("Synthetics", function () {
            it('Should find arg0/return', function (done) {
                testSource("function f(a){return a;} f(42); f('foo');", true, config, done);
            });
            it('Should find arg1/return', function (done) {
                testSource("function f(a,b){return b;} f(true, 42); f(true, 'foo');", true, config, done);
            });
            it('Should find arg0-prop-a/return', function (done) {
                testSource("function f(a){return a;} f({a: 42}); f({a: 'foo'});", true, config, done);
            });
            it('Should find arg0/return-prop-a', function (done) {
                testSource("function f(a){return {a: a};} f(42); f('foo');", true, config, done);
            });
            it('Should not find for arg0/return, other variant points', function (done) {
                testSource("function f(a,b){return a;} f({}, 42); f(true, 'foo');", false, config, done);
            });
            it('Should not find arg0/return, too few executions', function (done) {
                testSource("function f(a){return a;} f(42);", false, config, done);
            });
            it('Should not find arg0 (too few type-parameter-locations)', function (done) {
                testSource("function f(a){return true;} f(42); f('foo');", false, config, done);
            });
            it('Should find base/arg0', function (done) {
                testSource(
                    "function m(o){}\n" +
                    "var o1a = {a: 42, m: m};\n" +
                    "var o1b = {a: 78, m: m};\n" +
                    "var o2a = {b: 'foo', m: m};\n" +
                    "var o2b = {b: 'bar', m: m};\n" +
                    "o1a.m(o1b); o2a.m(o2b);", true, config, done);
            });

            it('Should find base/arg1', function (done) {
                testSource(
                    "function m(x, o){}\n" +
                    "var o1a = {a: 42, m: m};\n" +
                    "var o1b = {a: 78, m: m};\n" +
                    "var o2a = {b: 'foo', m: m};\n" +
                    "var o2b = {b: 'bar', m: m};\n" +
                    "o1a.m(true, o1b); o2a.m(false, o2b);", true, config, done);
            });

            it('Should find base-prop-a/arg0', function (done) {
                testSource(
                    "function m(o){}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m(87); o2.m('bar');", true, config, done);
            });

            it('Should find base-prop-b/arg0', function (done) {
                testSource(
                    "function m(o){}\n" +
                    "var o1 = {a: true, b: 42, m: m};\n" +
                    "var o2 = {a: false, b: 'foo', m: m};\n" +
                    "o1.m(87); o2.m('bar');", true, config, done);
            });

            it('Should find base/arg0-prop-b', function (done) {
                testSource(
                    "function m(o){ return; }\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m({b: o1}); o2.m({b: o2});", true, config, done);
            });

            it('Should find base-prop-a/arg1', function (done) {
                testSource(
                    "function m(x, o){}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m(true, 87); o2.m(false, 'bar');", true, config, done);
            });

            it('Should find base-prop-b/arg1', function (done) {
                testSource(
                    "function m(x, o){}\n" +
                    "var o1 = {a: true, b: 42, m: m};\n" +
                    "var o2 = {a: false, b: 'foo', m: m};\n" +
                    "o1.m(true, 87); o2.m(false, 'bar');", true, config, done);
            });

            it('Should find base-prop-0/arg0', function (done) {
                testSource(
                    "function m(o){}\n" +
                    "var o1 = {m: m};\n" +
                    "var o2 = {m: m};\n" +
                    "o1[0] = 42;\n" +
                    "o2[0] = 'foo';\n" +
                    "o1.m(87); o2.m('bar');", true, config, done);
            });

            it('Should find base-prop-1/arg0', function (done) {
                testSource(
                    "function m(o){}\n" +
                    "var o1 = {a: true, m: m};\n" +
                    "var o2 = {a: false, m: m};\n" +
                    "o1[1] = 42;\n" +
                    "o2[1] = 'foo';\n" +
                    "o1.m(87); o2.m('bar');", true, config, done);
            });

            it('Should find base-prop-0/arg1', function (done) {
                testSource(
                    "function m(x, o){}\n" +
                    "var o1 = {m: m};\n" +
                    "var o2 = {m: m};\n" +
                    "o1[0] = 42;\n" +
                    "o2[0] = 'foo';\n" +
                    "o1.m(true, 87); o2.m(false, 'bar');", true, config, done);
            });

            it('Should find base-prop-1/arg1', function (done) {
                testSource(
                    "function m(x, o){}\n" +
                    "var o1 = {a: true, m: m};\n" +
                    "var o2 = {a: false, m: m};\n" +
                    "o1[1] = 42;\n" +
                    "o2[1] = 'foo';\n" +
                    "o1.m(true, 87); o2.m(false, 'bar');", true, config, done);
            });

            it('Should find base-prop-a/return', function (done) {
                testSource(
                    "function m(o){return this.a;}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m(); o2.m();", true, config, done);
            });

            it('Should find base-prop-b/return', function (done) {
                testSource(
                    "function m(o){return this.b;}\n" +
                    "var o1 = {a: true, b: 42, m: m};\n" +
                    "var o2 = {a: false, b: 'foo', m: m};\n" +
                    "o1.m(); o2.m();", true, config, done);
            });
            it('Should find base-prop-0/return', function (done) {
                testSource(
                    "function m(o){return this[0];}\n" +
                    "var o1 = {m: m};\n" +
                    "var o2 = {m: m};\n" +
                    "o1[0] = 42;\n" +
                    "o2[0] = 'foo';\n" +
                    "o1.m(); o2.m();", true, config, done);
            });

            it('Should find base-prop-1/return', function (done) {
                testSource(
                    "function m(o){return this[1];}\n" +
                    "var o1 = {a: true, m: m};\n" +
                    "var o2 = {a: false, m: m};\n" +
                    "o1[1] = 42;\n" +
                    "o2[1] = 'foo';\n" +
                    "o1.m(); o2.m();", true, config, done);
            });
            it('Should find base-prop-a/return-prop-b', function (done) {
                testSource(
                    "function m(o){return {b: this.a};}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m(); o2.m();", true, config, done);
            });
            it('Should find base/return', function (done) {
                testSource(
                    "function m(o){return this;}\n" +
                    "var o1 = {x: 42, m: m};\n" +
                    "var o2 = {y: 'foo', m: m};\n" +
                    "o1.m(); o2.m();", true, config, done);
            });
            it('Should find base/return-prop-a', function (done) {
                testSource(
                    "function m(o){return {a: this};}\n" +
                    "var o1 = {x: 42, m: m};\n" +
                    "var o2 = {y: 'foo', m: m};\n" +
                    "o1.m(); o2.m();", true, config, done);
            });
            it('Should find base/arg0/return', function (done) {
                testSource(
                    "function m(arg){return arg;}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m(o1); o2.m(o2);", true, config, done);
            });
            it('Should find base-prop-a/arg0-prop-b/return-prop-c', function (done) {
                testSource(
                    "function m(arg){return {c: arg.b};}\n" +
                    "var o1 = {a: 42, m: m};\n" +
                    "var o2 = {a: 'foo', m: m};\n" +
                    "o1.m({b: 73}); o2.m({b: 'bar'});", true, config, done);
            });
        });
        describe("Reals", function () {
            it('Should find Array.prototype.indexOf', function (done) {
                testSource("var a = [1, 2, 3];\n" +
                    "var b = ['x', 'y', 'z'];\n" +
                    "a.indexOf(42); b.indexOf('foo');", true, config, done);
            });
            it('Should find Array.prototype.concat, simple', function (done) {
                testSource("var a = [1, 2, 3];\n" +
                    "var b = ['x', 'y', 'z'];\n" +
                    "a.concat(a); b.concat(b);", true, config, done);
            });
            it('Should find Array.prototype.concat', function (done) {
                testSource("var a = [1, 2, 3];\n" +
                    "var b = ['x', 'y', 'z'];\n" +
                    "a.concat([42]); b.concat(['foo']);", true, config, done);
            });
            it('Should find Array.prototype.push', function (done) {
                testSource("var a = [1, 2, 3];\n" +
                    "var b = ['x', 'y', 'z'];\n" +
                    "a.push(42); b.push('foo');", true, config, done);
            });
            it('Should find Array.prototype.pop', function (done) {
                testSource("var a = [1, 2, 3];\n" +
                    "var b = ['x', 'y', 'z'];\n" +
                    "a.pop(); b.pop();", true, config, done);
            });
        });
    });

    it('Should work for underscore', function (done) {
        this.timeout(60 * 1000);
        testFile("fixtures/underscore-singlefile.js", true, config, done);
    });
    it('Should work for paper example', function (done) {
        this.timeout(60 * 1000);
        testFile('fixtures/PaperExample1.js', true, config, done);
    });
    describe.skip("Benchmarks generics", function () {
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
