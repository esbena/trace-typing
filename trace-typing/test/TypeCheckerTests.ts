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

type MyTypeConfigType = (functionLatticeKind:TypeLattices.FunctionTypeLatticeKinds) => ValueTypeConfig
var inferenceConfigs /*:{[n:string]: MyTypeConfigType} */ = {
    genericInference: () => TypeLattices.makeFullIntersection(TypeLattices.FunctionTypeLatticeKinds.FunctionGenericTypeParameterOrLub),
    fullIntersection: TypeLattices.makeFullIntersection,
    simpleSubtyping: TypeLattices.makeSimpleSubtyping,
    simpleSubtypingWithUnion: TypeLattices.makeSimpleSubtypingWithUnion,
    SJS: TypeLattices.makeSJS
};

interface ExtractedExperimentConfiguration {
    fullTypeConfig: string, context: string, flowInsensitiveVariables: boolean
}

function testFile(file:string, expectedErrorCount:number, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    TraceMaker.getTraceFromSourceFile(file, function (err:any, trace:Trace) {
        TypeCheckerTester.testTrace(err, trace, expectedErrorCount, inferencerConfig, done, flowConfig);
    });
}
function testSource(source:string, expectedErrorCount:number, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    TraceMaker.getTraceFromSource(source, function (err:any, trace:Trace) {
        TypeCheckerTester.testTrace(err, trace, expectedErrorCount, inferencerConfig, done, flowConfig);
    });
}
describe("Std. TypeChecker unit tests", function () {
    this.timeout(5 * 1000);
    describe("sanityChecks", function () {
        var config = inferenceConfigs.fullIntersection; // choice is not important

        it('Should not find errors for empty program', function (done) {
            testSource("", 0, config, done, {});
        });
        it('Should not find errors for primitive program', function (done) {
            testSource("2 + 2;", 0, config, done, {});
        });
        it('Should allow valid property access', function (done) {
            testSource("({p: 42}).p", 0, config, done, {});
        });
        it('Should disallow invalid property access', function (done) {
            testSource("({}).p", 1, config, done, {});
        });
        it('Should allow allocations', function (done) {
            testSource("({})", 0, config, done, {});
        });
        it('Should allow function allocations', function (done) {
            testSource("(function(){})", 0, config, done, {});
        });
        it('Should allow function invocations', function (done) {
            testSource("(function(){})()", 0, config, done, {});
        });
        it('Should allow variable assignments', function (done) {
            testSource("(function(){ var a = 42; })()", 0, config, done, {});
        });
        it('Should allow variable redefinitions', function (done) {
            testSource("(function(){ var a = 42; a = 'foo';})()", 0, config, done, {});
        });
        it('Should allow valid property access through variable', function (done) {
            testSource("(function(){var o = {p: 42}; o.p})()", 0, config, done, {});
        });
        it('Should find true error', function (done) {
            testSource("({}).p", 1, config, done, {});
        });
        it('Should allow method invocation', function (done) {
            var config = inferenceConfigs.simpleSubtyping;
            var flowConfig = {flowInsensitiveVariables: true};
            testSource("" +
                "String.prototype.f = function () {};" +
                "String.prototype.f();",
                -1, config, done, flowConfig);
        });
    });
    describe("custom tests", function () {
        describe("fullIntersection", function () {
            var config = inferenceConfigs.fullIntersection;
            it('Should allow reassignment of property', function (done) {
                testSource("(function(){var o = {p: 87}; o.p = 42; o.p;})()", 0, config, done, {});
            });
            it('Should find nested intersection-caused error', function (done) {
                testSource("(function(){var o = {p: {}}; o.p = {p: 42}; o.p.p;})()", 1, config, done, {});
            });
        });
        describe("flow sensitive variables", function () {
            var config = inferenceConfigs.fullIntersection;
            var flowConfig = {flowInsensitiveVariables: false};
            it('Should allow reassignment of property #1', function (done) {
                testSource("(function(){var o = {p: 87}; var v = 'foo'; v = 42; o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
            it('Should allow reassignment of property #2', function (done) {
                testSource("(function(){var o = {p: 87}; var v = 42; v = 'foo'; o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
        });
        describe("flow insensitive variables & default initialization", function () {
            var config = inferenceConfigs.fullIntersection;
            var flowConfig = {flowInsensitiveVariables: true};
            it('Should find error in reassignment of property #1', function (done) {
                testSource("(function(){var o = {p: 42}; o.p;})()", 0, config, done, flowConfig);
            });
        });
        describe("flow insensitive variables", function () {
            var config = inferenceConfigs.simpleSubtyping;
            var flowConfig = {flowInsensitiveVariables: true};
            it('Should find error in reassignment of property #1', function (done) {
                testSource("(function(){var o = {p: 87}; var v = 'foo'; v = 42; o.p = v; o.p;})()", 1, config, done, flowConfig);
            });
            it('Should find error in reassignment of property #2', function (done) {
                testSource("(function(o, v){v = 42; o.p = v; o.p;})({p: 87}, 'foo')", 1, config, done, flowConfig);
            });
        });
        describe("context sensitive variables", function () {
            var config = inferenceConfigs.fullIntersection;
            var flowConfig = {contextInsensitiveVariables: false};
            it('Should allow reassignment of property #1', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id('foo'); v = id(42); o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
            it('Should allow reassignment of property #2', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id(42); v = id('foo'); o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
        });
        describe("context sensitive variables, generic function type instantiation", function () {
            var config = inferenceConfigs.genericInference;
            var flowConfig:PrecisionConfig = {callstackSensitiveVariables: {sensitivity: TypedTraceReplayer.CallStackSensitivity.GenericParameterInstantiations}};
            it('Should behave as if maximal context sensitivity was available #1', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id('foo'); v = id(42); o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
            it('Should behave as if maximal context sensitivity was available #2', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id(42); v = id('foo'); o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
            it('Should behave as if no context sensitivity was available #1', function (done) {
                // id is called with multiple arguments of different types: no good generic type
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id('foo', 99); v = id(42, true); o.p = v; o.p;})()", 1, config, done, flowConfig);
            });
            it("Should allow type parameter on base property and arg #1", function (done) {
                testSource('["foo"].push("bar"); [42].push(87);', 0, config, done, flowConfig);
            });
            it("Should allow type parameter on base property and arg property #1", function (done) {
                testSource('["foo"].concat(["bar"]); [42].concat([87]);', 0, config, done, flowConfig);
            });
            it("Should allow type parameter on base property (and return property) #1", function (done) {
                testSource('["foo"].pop(); [42].pop();', 0, config, done, flowConfig);
            });
        });
        describe("Should allow all generic identification examples", function () { // lots of copies from GenericTests.ts
            var config = inferenceConfigs.genericInference;
            var flowConfig:PrecisionConfig = {callstackSensitiveVariables: {sensitivity: TypedTraceReplayer.CallStackSensitivity.GenericParameterInstantiations}};
            describe("Synthetics", function () {
                it('Should find arg0/return', function (done) {
                    testSource("function f(a){return a;} f(42); f('foo');", 0, config, done, flowConfig);
                });
                it('Should find arg1/return', function (done) {
                    testSource("function f(a,b){return b;} f(true, 42); f(true, 'foo');", 0, config, done, flowConfig);
                });
                it('Should find arg0-prop-a/return', function (done) {
                    testSource("function f(a){return a;} f({a: 42}); f({a: 'foo'});", 0, config, done, flowConfig);
                });
                it('Should find arg0/return-prop-a', function (done) {
                    testSource("function f(a){return {a: a};} f(42); f('foo');", 0, config, done, flowConfig);
                });
                it.skip('Should not find for arg0/return, other variant points', function (done) {
                    testSource("function f(a,b){return a;} f({}, 42); f(true, 'foo');", 2 /* when top is not allowed during type checking */, config, done, flowConfig);
                });
                it('Should not find arg0/return, too few executions', function (done) {
                    testSource("function f(a){return a;} f(42);", 0, config, done, flowConfig);
                });
                it.skip('Should not find arg0 (too few type-parameter-locations)', function (done) {
                    testSource("function f(a){return true;} f(42); f('foo');", 2 /* when top is not allowed during type checking */, config, done, flowConfig);
                });
                it('Should find base/arg0', function (done) {
                    testSource(
                        "function m(o){}\n" +
                        "var o1a = {a: 42, m: m};\n" +
                        "var o1b = {a: 78, m: m};\n" +
                        "var o2a = {b: 'foo', m: m};\n" +
                        "var o2b = {b: 'bar', m: m};\n" +
                        "o1a.m(o1b); o2a.m(o2b);", 0, config, done, flowConfig);
                });

                it('Should find base/arg1', function (done) {
                    testSource(
                        "function m(x, o){}\n" +
                        "var o1a = {a: 42, m: m};\n" +
                        "var o1b = {a: 78, m: m};\n" +
                        "var o2a = {b: 'foo', m: m};\n" +
                        "var o2b = {b: 'bar', m: m};\n" +
                        "o1a.m(true, o1b); o2a.m(false, o2b);", 0, config, done, flowConfig);
                });

                it('Should find base-prop-a/arg0', function (done) {
                    testSource(
                        "function m(o){}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m(87); o2.m('bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-b/arg0', function (done) {
                    testSource(
                        "function m(o){}\n" +
                        "var o1 = {a: true, b: 42, m: m};\n" +
                        "var o2 = {a: false, b: 'foo', m: m};\n" +
                        "o1.m(87); o2.m('bar');", 0, config, done, flowConfig);
                });

                it('Should find base/arg0-prop-b', function (done) {
                    testSource(
                        "function m(o){ return; }\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m({b: o1}); o2.m({b: o2});", 0, config, done, flowConfig);
                });

                it('Should find base-prop-a/arg1', function (done) {
                    testSource(
                        "function m(x, o){}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m(true, 87); o2.m(false, 'bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-b/arg1', function (done) {
                    testSource(
                        "function m(x, o){}\n" +
                        "var o1 = {a: true, b: 42, m: m};\n" +
                        "var o2 = {a: false, b: 'foo', m: m};\n" +
                        "o1.m(true, 87); o2.m(false, 'bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-0/arg0', function (done) {
                    testSource(
                        "function m(o){}\n" +
                        "var o1 = {m: m};\n" +
                        "var o2 = {m: m};\n" +
                        "o1[0] = 42;\n" +
                        "o2[0] = 'foo';\n" +
                        "o1.m(87); o2.m('bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-1/arg0', function (done) {
                    testSource(
                        "function m(o){}\n" +
                        "var o1 = {a: true, m: m};\n" +
                        "var o2 = {a: false, m: m};\n" +
                        "o1[1] = 42;\n" +
                        "o2[1] = 'foo';\n" +
                        "o1.m(87); o2.m('bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-0/arg1', function (done) {
                    testSource(
                        "function m(x, o){}\n" +
                        "var o1 = {m: m};\n" +
                        "var o2 = {m: m};\n" +
                        "o1[0] = 42;\n" +
                        "o2[0] = 'foo';\n" +
                        "o1.m(true, 87); o2.m(false, 'bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-1/arg1', function (done) {
                    testSource(
                        "function m(x, o){}\n" +
                        "var o1 = {a: true, m: m};\n" +
                        "var o2 = {a: false, m: m};\n" +
                        "o1[1] = 42;\n" +
                        "o2[1] = 'foo';\n" +
                        "o1.m(true, 87); o2.m(false, 'bar');", 0, config, done, flowConfig);
                });

                it('Should find base-prop-a/return', function (done) {
                    testSource(
                        "function m(o){return this.a;}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });

                it('Should find base-prop-b/return', function (done) {
                    testSource(
                        "function m(o){return this.b;}\n" +
                        "var o1 = {a: true, b: 42, m: m};\n" +
                        "var o2 = {a: false, b: 'foo', m: m};\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });
                it('Should find base-prop-0/return', function (done) {
                    testSource(
                        "function m(o){return this[0];}\n" +
                        "var o1 = {m: m};\n" +
                        "var o2 = {m: m};\n" +
                        "o1[0] = 42;\n" +
                        "o2[0] = 'foo';\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });

                it('Should find base-prop-1/return', function (done) {
                    testSource(
                        "function m(o){return this[1];}\n" +
                        "var o1 = {a: true, m: m};\n" +
                        "var o2 = {a: false, m: m};\n" +
                        "o1[1] = 42;\n" +
                        "o2[1] = 'foo';\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });
                it('Should find base-prop-a/return-prop-b', function (done) {
                    testSource(
                        "function m(o){return {b: this.a};}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });
                it('Should find base/return', function (done) {
                    testSource(
                        "function m(o){return this;}\n" +
                        "var o1 = {x: 42, m: m};\n" +
                        "var o2 = {y: 'foo', m: m};\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });
                it('Should find base/return-prop-a', function (done) {
                    testSource(
                        "function m(o){return {a: this};}\n" +
                        "var o1 = {x: 42, m: m};\n" +
                        "var o2 = {y: 'foo', m: m};\n" +
                        "o1.m(); o2.m();", 0, config, done, flowConfig);
                });
                it('Should find base/arg0/return', function (done) {
                    testSource(
                        "function m(arg){return arg;}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m(o1); o2.m(o2);", 0, config, done, flowConfig);
                });
                it('Should find base-prop-a/arg0-prop-b/return-prop-c', function (done) {
                    testSource(
                        "function m(arg){return {c: arg.b};}\n" +
                        "var o1 = {a: 42, m: m};\n" +
                        "var o2 = {a: 'foo', m: m};\n" +
                        "o1.m({b: 73}); o2.m({b: 'bar'});", 0, config, done, flowConfig);
                });
            });
            describe("Reals", function () {
                it('Should find Array.prototype.indexOf', function (done) {
                    testSource("var a = [1, 2, 3];\n" +
                        "var b = ['x', 'y', 'z'];\n" +
                        "a.indexOf(42); b.indexOf('foo');", 0, config, done, flowConfig);
                });
                it('Should find Array.prototype.concat, simple', function (done) {
                    testSource("var a = [1, 2, 3];\n" +
                        "var b = ['x', 'y', 'z'];\n" +
                        "a.concat(a); b.concat(b);", 0, config, done, flowConfig);
                });
                it('Should find Array.prototype.concat', function (done) {
                    testSource("var a = [1, 2, 3];\n" +
                        "var b = ['x', 'y', 'z'];\n" +
                        "a.concat([42]); b.concat(['foo']);", 0, config, done, flowConfig);
                });
                it('Should find Array.prototype.push', function (done) {
                    testSource("var a = [1, 2, 3];\n" +
                        "var b = ['x', 'y', 'z'];\n" +
                        "a.push(42); b.push('foo');", 0, config, done, flowConfig);
                });
                it('Should find Array.prototype.pop', function (done) {
                    testSource("var a = [1, 2, 3];\n" +
                        "var b = ['x', 'y', 'z'];\n" +
                        "a.pop(); b.pop();", 0, config, done, flowConfig);
                });
            });
        });

        describe("context insensitive variables", function () {
            var config = inferenceConfigs.fullIntersection;
            var flowConfig = {contextInsensitiveVariables: true};
            it('Shoud allow calls with different arguments', function (done) {
                testSource("(function(){ function id(v){return v;} id(42); id('foo');})()", 0, config, done, flowConfig);
            });
            it('Should find error in reassignment of property #1', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id('foo'); v = id(42); o.p = v; o.p;})()", 1, config, done, flowConfig);
            });
            it('Should allow reassignment of property #1', function (done) {
                testSource("(function(){ function id(v){return v;} var o = {p: 87}; var v = id(42); v = id('foo'); o.p = v; o.p;})()", 0, config, done, flowConfig);
            });
        });
        describe("Paper", function () {
            var config = inferenceConfigs.simpleSubtyping;
            var flowConfig = {flowInsensitiveVariables: false, contextInsensitiveVariables: true};
            it('Should handle PaperExample1', function (done) {
                testFile('fixtures/PaperExample1.js', 1, config, done, flowConfig);
            });
        });
        describe("calls to non-functions", function () {
            var config = inferenceConfigs.simpleSubtypingWithUnion
            var flowConfig = {flowInsensitiveVariables: true, contextInsensitiveVariables: false};
            it("Should allow function invocations", function (done) {
                testSource("var f = function(){}; f()", 0, config, done, flowConfig);
            });
            it("Should not allow function constructor invocations", function (done) {
                testSource("var f = function(){}; new f()", 0, config, done, flowConfig);
            });
            it("Should allow invocations of object-merge-erased functions", function (done) {
                testSource("var f = {}; f = function(){}; f()", 0, config, done, flowConfig);
            });
            it("Should almost allow constructor invocations of object-merge-erased functions", function (done) {
                testSource("var f = {}; f = function(){}; new f()", 1, config, done, flowConfig);
            });
            it("Should allow invocations of primitive-merge-erased functions", function (done) {
                testSource("var f = 42; f = function(){}; f()", 0, config, done, flowConfig);
            });
            it("Should allow invocations of primitive-merge-erased functions", function (done) {
                testSource("var f = 42; f = function(){}; new f()", 0, config, done, flowConfig);
            });
        });
        describe("module.exports examples", function () {
            var config = inferenceConfigs.simpleSubtypingWithUnion
            var flowConfig = {flowInsensitiveVariables: false, contextInsensitiveVariables: false};
            it('Should allow call to `modules.export = function(){}`', function (done) {
                testFile('fixtures/ModuleExports1.js', 0, config, done, flowConfig);
            });
            it('Should not allow constructor call to `modules.export = function(){}`', function (done) {
                // no prototype property
                testFile('fixtures/ModuleExports2.js', 1, config, done, flowConfig);
            });
        });
        describe("Prototyping in xml2js", function () {
            var config = inferenceConfigs.simpleSubtypingWithUnion;
            var flowConfig = {flowInsensitiveVariables: true, contextInsensitiveVariables: true};
            it('Should almost handle PrototypingExample1', function (done) {
                testFile('fixtures/xml2js_PrototypingExample1.js', 1 /* due to constructor call requiring .prototype on merged object ... */, config, done, flowConfig);
            });
            it('Should handle PrototypingExample2', function (done) {
                testFile('fixtures/xml2js_PrototypingExample2.js', 0, config, done, flowConfig);
            });
            it('Should handle PrototypingExample3', function (done) {
                testFile('fixtures/xml2js_PrototypingExample3.js', 0, config, done, flowConfig);
            });
            it('Should almost handle PrototypingExample4', function (done) {
                testFile('fixtures/xml2js_PrototypingExample4.js', 2 /* due to constructor call requiring .prototype on merged object ... */, config, done, flowConfig);
            });
        });
        describe("Class hierarchies in transpiled code", function () {
            var configs = [{
                config: inferenceConfigs.simpleSubtypingWithUnion,
                name: 'simpleSubtypingWithUnion'
            }, {
                config: inferenceConfigs.fullIntersection,
                name: 'fullIntersection'
            }];
            var flowConfig = {flowInsensitiveVariables: false, contextInsensitiveVariables: false};
            var languages = ['coffeescript', 'typescript'];
            var cases = ['Super', 'SubNoExports', 'Sub', 'InstantiateSuper', 'InstantiateSubNoExports', 'InstantiateSub', 'CallSuperMethodThroughSuper', 'CallSubMethodThroughSub', 'CallSuperMethodThroughSub'];
            configs.forEach(configAndName => describe(util.format("In configuration %s", configAndName.name), function () {
                var config = configAndName.config;
                languages.forEach(l => describe(l, function () {
                    cases.forEach(c => {
                        it("Should handle " + c, function (done) {
                            testFile(util.format('fixtures/%s-hierarchy/%s.js', l, c), 0, config, done, flowConfig);
                        })
                    });
                }));
            }))
        });
        describe("Fixpointing", function () {
            var config = inferenceConfigs.simpleSubtyping;
            var flowConfig = {flowInsensitiveVariables: true, contextInsensitiveVariables: true};
            it('Should fixpoint on same argument', function (done) {
                testSource("function f(v){return v;} f(42); f(42);", 0, config, done, flowConfig);
            });
            it('Should fixpoint on different arguments', function (done) {
                testSource("function f(){} f(42); f('foo');", 0, config, done, flowConfig);
            });
            it('Should fixpoint on different arguments, in context of changing variables', function (done) {
                // type error due to call with Top argument
                testSource("(function(r){function f(v){return v;} f(r); r = f(42); r = f('foo'); r = f(f);})(true);", 1, config, done, flowConfig);
            });
        });
        describe("Mail questions", function () {
            this.timeout(0);
            it('Should answer mail question 1a', function (done) {
                var config = () => TypeLattices.makeSimpleSubtyping(TypeLattices.FunctionTypeLatticeKinds.FunctionPointwiseLub);
                var flowConfig = {};
                testFile('fixtures/mail-question-1a.js', 1, config, done, flowConfig);
            });
            it('Should answer mail question 1b', function (done) {
                var config = () => TypeLattices.makeSimpleSubtyping(TypeLattices.FunctionTypeLatticeKinds.FunctionPointwiseLub);
                var flowConfig = {flowInsensitiveVariables: true};
                testFile('fixtures/mail-question-1b.js', 1, config, done, flowConfig);
            });
        });
    });
})
;
interface ErrorAndWarningCounts {
    errors: number
    warnings: number
}

var warningGroup:TypeChecker.ConstraintKinds[] = [/*TypeChecker.ConstraintKinds.IsNotTop*/];
// the rest of the violated constraint kinds are errors
var errorGroup:TypeChecker.ConstraintKinds[] = [];
var SJSErrorGroup = [TypeChecker.ConstraintKinds.IsClassificationValidAccess, TypeChecker.ConstraintKinds.IsNotClassifiedAsObject, TypeChecker.ConstraintKinds.PropertyIsWritable, TypeChecker.ConstraintKinds.PrototypalAssignment, TypeChecker.ConstraintKinds.PrototypePropertyInvariance, TypeChecker.ConstraintKinds.IsAbstractObject];
var SJSSpecificsOnly = false;
if (SJSSpecificsOnly) {
    errorGroup = SJSErrorGroup;
} else {
    for (var k in TypeChecker.ConstraintKinds) {
        k = parseInt(k);
        if (!isNaN(k)) {
            if (warningGroup.indexOf(k) === -1) {
                errorGroup.push(k);
            }
        }
    }
}

class FunctionTypeConfiguration {
    constructor(public functionLatticeKind:number, // enum::FunctionTypeLatticeKinds
                public description:string,
                public contextInsensitiveVariables:boolean,
                public callstackSensitiveVariables:CallStackSensitivityConfig) {
    }
}

var useFunctionIIDSforErrorCounts = false; // TODO play with this
function staticErrorCount(numbers:StaticDynamicNumberPair):number {
    if (useFunctionIIDSforErrorCounts) {
        return numbers.StaticFunctions;
    }
    return numbers.Static;
}
describe.only   ("Type check traces and display table", function () {
    var mode = 'RUN';
    //var mode = 'DISPLAY';
    //var mode = 'PIVOT';
    //var mode = 'KIND';
    describe("Type check everything ", function () {
        if (mode !== 'RUN') {
            return;
        }
        this.timeout(5 * 60 * 1000);
        TestUtil.getBenchmarkTraceFiles().forEach(function (file) {

            var experiment:string;

            //experiment = "SANITY";
            //experiment = "COMPARISONS";
            //experiment = "SMALL-COMPARISONS";
            experiment = "SJS";

            var allTypes:[(functionLatticeKind?:TypeLattices.FunctionTypeLatticeKinds) => ValueTypeConfig, string][];
            var allFunctionTypes:FunctionTypeConfiguration[];
            var allVariableFlowInsensitivities:boolean[];
            switch (experiment) {
                case "SMALL-COMPARISONS":
                    allTypes = [
//                [inferenceConfigs.fullIntersection, 'intersection']
                        [inferenceConfigs.simpleSubtyping, 'simpleSubtyping']
//                        , [inferenceConfigs.simpleSubtypingWithUnion, 'simpleSubtypingWithUnion']
//                , [inferenceConfigs.SJS, 'SJS']
                    ];
                    allFunctionTypes = [
                        //new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionGenericTypeParameterOrLub, "GenericOrSingle", false, {sensitivity: TypedTraceReplayer.CallStackSensitivity.GenericParameterInstantiations})
                        new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctions", false, undefined)
//                        , new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionPointwiseLub, "SingleFunctions", true, undefined)
                    ]
                    ;
                    allVariableFlowInsensitivities = [
//                false
                        true
                    ];
                    break;
                case "COMPARISONS":
                    allTypes = [
//                [inferenceConfigs.fullIntersection, 'intersection']
                        [inferenceConfigs.simpleSubtyping, 'simpleSubtyping']
                        , [inferenceConfigs.simpleSubtypingWithUnion, 'simpleSubtypingWithUnion']
//                , [inferenceConfigs.SJS, 'SJS']
                    ];
                    allFunctionTypes = [
                        new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctions", false, undefined)
                        //, new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctionsWCallStack", false, {sensitivity: TypedTraceReplayer.CallStackSensitivity.ParameterValues})
                        //, new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctionsWCallStack-1", false, {height: 1, sensitivity: TypedTraceReplayer.CallStackSensitivity.ParameterValues})
                        , new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionGenericTypeParameterOrLub, "GenericOrSingle", false, {sensitivity: TypedTraceReplayer.CallStackSensitivity.GenericParameterInstantiations})
                        , new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionPointwiseLub, "SingleFunctions", true, undefined)
                    ]
                    ;
                    allVariableFlowInsensitivities = [
//                false
                        true
                    ];
                    break;
                case "SJS":
                    allTypes = [
                        [inferenceConfigs.SJS, 'SJS']
                    ];
                    allFunctionTypes = [
                        new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctions", false, undefined)
                    ]
                    ;
                    allVariableFlowInsensitivities = [
                        false
                    ];
                    break;
                case "SANITY":
                    allTypes = [
                        [inferenceConfigs.simpleSubtyping, 'simpleSubtyping']
                    ];
                    allFunctionTypes = [
                        new FunctionTypeConfiguration(TypeLattices.FunctionTypeLatticeKinds.FunctionIntersection, "IntersectionFunctions", false, undefined)
                    ]
                    ;
                    allVariableFlowInsensitivities = [
                        true
                    ];
                    break;
                default:
                    throw new Error("Unhandled experiment name: " + experiment);
            }
            var testCounter = 0;
            allTypes.forEach((types:[(functionLatticeKind:TypeLattices.FunctionTypeLatticeKinds)=>ValueTypeConfig, string])=> {
                allFunctionTypes.forEach((functionTypeConfiguration:FunctionTypeConfiguration)=> {
                    allVariableFlowInsensitivities.forEach(vars => {
                        var flowConfig:PrecisionConfig = {
                            flowInsensitiveVariables: vars,
                            contextInsensitiveVariables: functionTypeConfiguration.contextInsensitiveVariables,
                            callstackSensitiveVariables: functionTypeConfiguration.callstackSensitiveVariables
                        };
                        var typeSystemDescription = ('config#' + testCounter++ + ': ') + types[1] + ' with ' + functionTypeConfiguration.description + " using " + (vars ? "flowInsensitive" : "flowSensitive") + " vars";
                        it("... in particular: " + path.basename(file) + " " + typeSystemDescription, function (done) {
                            var traceImporter:TraceImporter.TraceImporter = new TraceImporter.TraceImporter();
                            traceImporter.import(file, function (err:any, imported:TraceImport) {
                                if (err) {
                                    done(err);
                                    return;
                                }
                                TypeCheckerTester.testTrace(err, imported.trace, -1, () => types[0](functionTypeConfiguration.functionLatticeKind), done, flowConfig, true, typeSystemDescription, types[1] === 'SJS');
                            });
                        });
                    });
                });
            });
        });
    });


    function extractConfigurationFromDescriptionString(description:string):ExtractedExperimentConfiguration {
        var match = description.match(/config#.*: (.*) with (.*) using (.*) vars/);
        return {fullTypeConfig: match[1], context: match[2], flowInsensitiveVariables: match[3] === "flowInsensitive"};
    }

    it("Make kind tables", function (done) {
        // FIXME full of terrible hacks! Should really refactor!!
        if (mode !== 'KIND') {
            done();
            return;
        }
        PersistentResults.load(PersistentResults.ExperimentResultKinds.TypeChecksResult, (results:AnnotatedExperimentResults<TypeChecksResult>[])=> {
            results = results.filter(r => r.sources.some(f => f !== null && TestUtil.getBigApps().some(a => f.indexOf(a) !== -1)));
            var bySourceCSVLines = new Map<string, string[]>();
            results.forEach((r:AnnotatedExperimentResults<TypeChecksResult>) => {
                // parse the fully qualified source paths for each file
                var source = r.sources.filter(s => s !== null && !!s.match(/\/node_modules\//)).map(s => {
                    var match = s.match(/\/([^/]+)\/node_modules\//);
                    return match[1 /* pick first */];
                })[0 /* index should not matter */];

                if (!bySourceCSVLines.has(source)) {
                    bySourceCSVLines.set(source, []);
                }

                // parse the description format made in TypeCheckerTester.ts (silly)
                var descriptionComponents = extractConfigurationFromDescriptionString(r.description);

                var fullTypeConfig = descriptionComponents.fullTypeConfig;
                var shortTypeConfig:string;
                switch (fullTypeConfig) {
                    case 'intersection':
                        shortTypeConfig = 'simple'; // XXX seems like a weird naming mapping?!
                        break;
                    case 'simpleSubtyping':
                        shortTypeConfig = 'subtyping';
                        break;
                    case 'simpleSubtypingWithUnion':
                        shortTypeConfig = 'unions';
                        break;
                    case 'SJS':
                        shortTypeConfig = 'SJS';
                        break;
                    default:
                        throw new Error("Unhandled type case: " + fullTypeConfig);
                }
                if (shortTypeConfig !== 'SJS') {
                    return;
                }
                r.results.forEach((result:TypeChecksResult) => {
                    for (var kind in result.data) {
                        if (SJSErrorGroup.indexOf(+kind) !== -1) {
                            var line = util.format('"%s", "%d";', TypeChecker.ConstraintKinds[kind], staticErrorCount(result.data[kind]));
                            bySourceCSVLines.get(source).push(line);
                        }
                    }
                });
                // sort lines for prettyness
                var outDir = ConfigLoader.load().experimentResultDirectory;
                console.log('%s:', source);
                bySourceCSVLines.forEach((lines:string[], source:string) => {
                    lines.sort();
                    lines.forEach(l => console.log("  %s", l));
                    var filename = path.resolve(outDir, source + "-SJS-checks.csv");
                    fs.writeFileSync(filename, lines.join('\n'));
                });

            });
            done();
        });
    });

    it("Make pivot tables", function (done) {
        if (mode !== 'PIVOT') {
            done();
            return;
        }
        function countErrorsAndWarnings(results:TypeChecksResult[]):ErrorAndWarningCounts {
            var counts = {errors: 0, warnings: 0};
            results.forEach((r:TypeChecksResult) => {
                errorGroup.forEach(e => counts.errors += staticErrorCount(r.data[e]));
                warningGroup.forEach(w => counts.warnings += staticErrorCount(r.data[w]));
            });

            return counts;
        }

        PersistentResults.load(PersistentResults.ExperimentResultKinds.TypeChecksResult, (results:AnnotatedExperimentResults<TypeChecksResult>[])=> {
            results = results.filter(r => r.sources.some(f => f !== null && TestUtil.getBigApps().some(a => f.indexOf(a) !== -1)));
            var bySourceCSVLines = new Map<string, string[]>();
            results.forEach((r:AnnotatedExperimentResults<TypeChecksResult>) => {
                // parse the fully qualified source paths for each file
                var source = r.sources.filter(s => s !== null && !!s.match(/\/node_modules\//)).map(s => {
                    var match = s.match(/\/([^/]+)\/node_modules\//);
                    return match[1 /* pick first */];
                })[0 /* index should not matter */];

                if (!bySourceCSVLines.has(source)) {
                    bySourceCSVLines.set(source, []);
                }

                // parse the description format made in TypeCheckerTester.ts (silly)
                var descriptionComponents = extractConfigurationFromDescriptionString(r.description);

                var shortTypeConfig:string;
                switch (descriptionComponents.fullTypeConfig) {
                    case 'intersection':
                        shortTypeConfig = 'simple'; // XXX seems like a weird naming mapping?!
                        break;
                    case 'simpleSubtyping':
                        shortTypeConfig = 'subtyping';
                        break;
                    case 'simpleSubtypingWithUnion':
                        shortTypeConfig = 'unions';
                        break;
                    case 'SJS':
                        shortTypeConfig = 'SJS';
                        break;
                    default:
                        throw new Error("Unhandled type case: " + descriptionComponents.fullTypeConfig);
                }

                var contextSensitivity:string;
                switch (descriptionComponents.context) {
                    case "GenericOrSingle":
                        contextSensitivity = "poly";
                        break;
                    case "IntersectionFunctions":
                        contextSensitivity = "full";
                        break;
                    case "SingleFunctions":
                        contextSensitivity = "none";
                        break;
                    default:
                        throw new Error("Unhandled context case: " + descriptionComponents.context);
                }
                var flowSensitivity = (descriptionComponents.flowInsensitiveVariables ? 'fi' : 'fs');
                var precisionConfig = util.format("%s %s", flowSensitivity, contextSensitivity);

                var line = util.format('"%s", "%s", "%d";', shortTypeConfig, precisionConfig, countErrorsAndWarnings(r.results).errors);
                // console.log('csving: %s', line);
                bySourceCSVLines.get(source).push(line);
            });
            // sort lines for prettyness
            var outDir = ConfigLoader.load().experimentResultDirectory;
            bySourceCSVLines.forEach((lines:string[], source:string) => {
                function cmp(l1:string, l2:string, target:string) {
                    return -1 * (Math.max(0, l1.indexOf(target)) - Math.max(0, l2.indexOf(target)));
                }

                lines.sort((l1, l2) => {
                    var subtypingCmp = cmp(l1, l2, "subtyping");
                    if(subtypingCmp !== 0){
                        return subtypingCmp;
                    }
                    var unionsCmp = cmp(l1, l2, "unions");
                    if(unionsCmp !== 0){
                        return unionsCmp;
                    }

                    var noneCmp = cmp(l1, l2, 'none');
                    if(noneCmp !== 0){
                        return noneCmp;
                    }
                    var polyCmp = cmp(l1, l2, 'poly');
                    if(polyCmp !== 0){
                        return polyCmp;
                    }
                    var intersectCmp = cmp(l1, l2, 'intersect');
                    if(intersectCmp !== 0){
                        return intersectCmp;
                    }
                    return 0;
                });
                lines.forEach(l => console.log("  %s", l));
                var filename = path.resolve(outDir, source + "-static-error-counts.csv");
                fs.writeFileSync(filename, lines.join('\n'));
            });

            done();
        });
    });

    it("Display table & charts", function (done) {
        if (mode !== 'DISPLAY') {
            done();
            return;
        }
        // TODO refactor some of this to separate file
        // FIXME tables need 'enough' data to be structured correct, e.g. a single configuration  will be buggy..
        this.timeout(5 * 60 * 1000);
        PersistentResults.load(PersistentResults.ExperimentResultKinds.TypeChecksResult, (results:AnnotatedExperimentResults<TypeChecksResult>[])=> {
            results = results.filter(r => r.sources.some(f => f !== null && !TestUtil.ignoreFile(f)));
            function makeTable(location:string, constraintKind:TypeChecker.ConstraintKinds) {
                var rows:string[][] = [];
                groupedBySources_keys.forEach(sources => {
                        var rowData = groupedBySourcesAndThenDescription.get(sources);
                        var row = descriptions.map(description => {
                            var cellData = rowData.get(description);
                            return cellData ? (<any>cellData.data)[constraintKind][location] + '' : "??";
                        });
                        rows.push([path.basename(path.dirname(path.dirname(sources))) + '/' + path.basename(path.dirname(sources))].concat(row));
                    }
                );
                var table:Table = {
                    title: location + ' ' + TypeChecker.ConstraintKinds[constraintKind] + ' failures',
                    headers: ["source"].concat(descriptions.map(desc => desc.replace("flowInsensitiveVariables", "fIV").replace("contextInsensitiveVariables", "cIV"))),
                    rows: rows
                };
                return table;
            }

            function makeStackedGroupedBarCharts(location:string):StackedGroupedBarCharts {
                var groups = [errorGroup, warningGroup];
                var barchartData:BarChartData[] = groupedBySources_keys.map(sources => {
                    var sourceData = groupedBySourcesAndThenDescription.get(sources);
                    var rows = descriptions.map((description:any)=> {
                        var groupData:TypeChecksResult = sourceData.get(description);
                        var row:any[];
                        if (groupData) {
                            var numberRow:number[] = [];
                            groups.forEach(group =>
                                group.forEach(n => {
                                    var data = groupData.data;
                                    var value:number = (<any>data)[n][location];
                                    if (description.indexOf("flowsensitive") !== -1) {
                                        value = undefined;
                                    }
                                    numberRow.push(value || 0);
                                })
                            );

                            row = [description].concat(numberRow);
                        }
                        var dummyRowLength = warningGroup.length + errorGroup.length + 1;
                        if (!row || row.length != dummyRowLength) {
                            console.log("row.length %d for %s", row ? row.length : row, sources);
                            row = [description];
                            while (row.length !== dummyRowLength) {
                                row.push(-1);
                            }
                        }
                        return row;
                    });
                    var simpleSources:string;
                    var sourceMatch = sources.match(/\/([^/]+)\/node_modules\//);
                    if (sourceMatch) {
                        simpleSources = sourceMatch[1];
                    } else {
                        simpleSources = sources;
                    }
                    var chart:BarChartData = {
                        rows: rows,
                        title: 'Type errors and warnings for ' + simpleSources
                    };
                    return chart;
                });
                var columnDescriptions:{
                    type: string
                    description: string
                }[] = [];
                groups.forEach(group =>
                    group.forEach(n => {
                        columnDescriptions.push({
                            type: 'number',
                            description: TypeChecker.ConstraintKinds[n] + ' ' + location
                        });
                    })
                );

                var columnGroupings = [errorGroup.length, warningGroup.length];
                return {
                    barchartData: barchartData,
                    columnDescriptions: columnDescriptions,
                    columnGroupings: columnGroupings
                };
            }

            var groupedBySourcesAndThenDescription = new Map<string, Map<string, TypeChecksResult>>();
            var groupedBySources_keys:string[] = [];
            results.forEach(ar => {
                ar.sources.sort();
                var key = ar.sources.join(":");
                if (!groupedBySourcesAndThenDescription.has(key)) {
                    groupedBySourcesAndThenDescription.set(key, new Map<string, TypeChecksResult>());
                    groupedBySources_keys.push(key);
                }
                groupedBySourcesAndThenDescription.get(key).set(ar.description, ar.results[0]);
            });

            var descriptions:string[] = [];
            results.forEach(ar => {
                if (descriptions.indexOf(ar.description) === -1) {
                    descriptions.push(ar.description);
                }
            });
            descriptions.sort();

            var locations = ['Static', 'StaticFunctions', 'Dynamic'];

            //locations.forEach(location => constraintKinds.forEach(constraintKind => {
            //    var table = makeTable(location, constraintKind);
            //    var lines: string[]= [];
            //    lines.push(table.headers.map(h => '"' + h.replace(/"/g, '') + '"').join(','));
            //    table.rows.forEach(row => lines.push(row.map(cell => '"' + cell.replace(/"/g, '') + '"').join(',')));
            //    var filename = "/Users/e.andreasen/tmp/csvs/" + location + "-" + TypeChecker.ConstraintKinds[constraintKind] + ".csv";
            //    fs.writeFileSync(filename, lines.join('\n'));
            //    console.log("Saved to %s", filename);
            //    //MetaInformationExplainerImpl.displayTableInBrowser(table, function () {
            //    //})
            //}));
            MetaInformationExplainerImpl.displayStackedGroupedBarChartsInBrowser(makeStackedGroupedBarCharts(locations[0]), function () {
                MetaInformationExplainerImpl.displayStackedGroupedBarChartsInBrowser(makeStackedGroupedBarCharts(locations[1]), function () {
                    done();
                });
            });
            //});
        });
    });
});
