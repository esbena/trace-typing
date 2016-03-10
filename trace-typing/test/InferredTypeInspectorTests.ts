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

// no equals on arrays -> no use in maps... (silly javascript)
type EqualityArray = string;
class ObjectTypeNames {
    private type2path:Map<ObjectType, string[]>;
    private static preferredPaths = ObjectTypeNames.makePreferredPaths();

    /**
     * Avoids naming types with user-defined names that happen to have a shorter path from the root.
     * NB: this does not completely avoid silly names
     */
    private static makePreferredPaths() {
        var set = new Set<EqualityArray>();
        // exploit that we are imlementing this in JavaScript :)
        var roots:{
            [x:string]: Object
        } = {
            'Function.prototype': Function.prototype,
            'Object': Object,
            'Object.prototype': Object.prototype,
            'String.prototype': String.prototype,
            'Array.prototype': Array.prototype
        };
        for (var rootName in roots) {
            for (var p in roots[rootName]) {
                set.add(rootName + "." + p);
            }
        }
        return set;
    }

    constructor(root:ObjectType) {
        this.type2path = new Map<ObjectType, string[]>()
        ObjectTypeNames.buildType2path(root, [], this.type2path);
    }

    private static buildType2path(type:ObjectType, path:string[], type2path:Map<ObjectType, string[]>) {
        if (type2path.has(type)) {
            var currentPath = type2path.get(type);
            var doesNotPreferCurrentPath = !ObjectTypeNames.preferredPaths.has(ObjectTypeNames.toPathKey(currentPath));
            var prefersNewPath = (currentPath.length > path.length || ObjectTypeNames.preferredPaths.has(ObjectTypeNames.toPathKey(path)));
            if (doesNotPreferCurrentPath && prefersNewPath) {
                type2path.set(type, path);
            }
        } else {
            type2path.set(type, path);
            var keys = Object.keys(type.properties).sort();
            keys.forEach(p => {
                var propertyType = type.properties[p];
                if (TypeImpls.TupleAccess.isObject(propertyType)) {
                    ObjectTypeNames.buildType2path(TypeImpls.TupleAccess.getObject(propertyType), path.concat(p), type2path);
                }
            });
        }
    }

    private static toPathKey(path:string[]):EqualityArray {
        return path.join(".");
    }

    public getName(type:ObjectType):string[] {
        return this.type2path.get(type);
    }
}
function testTrace(err:any, trace:Trace, typeName:string, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    if (err) {
        done(err);
        throw err;
    }
    var explainer = new MetaInformationExplainerImpl(trace.iidMap);

    try {
        var traceReplayResults = TraceReplayer.replayTrace(trace);
        var typeLatticePair = inferencerConfig();

        var results = TypedTraceReplayer.replayTrace(traceReplayResults.variableValues, traceReplayResults.variableList, trace.statements, flowConfig, typeLatticePair, explainer);


        var globalVariables = traceReplayResults.variableList.filter(v => v.named && v.name === 'global');
        console.log("Found %d 'global' variables, picking the first:", globalVariables.length);
        var root = TypeImpls.TupleAccess.getObject(results.propagatedEnv.read(globalVariables[0]));
        var typeNames = new ObjectTypeNames(root);
        var canonicalNamer = (t:ObjectType):string => {
            var name = typeNames.getName(t);
            if (name === undefined) {
                return undefined;
            }
            var qualified: string;
            if (name.length === 0) {
                qualified = "-GLOBAL-";
            } else {
                qualified = name.join(".");
            }
            // console.log("Name for %s is %s", TypeImpls.toPrettyString(new TypeImpls.TupleTypeImpl([t])),qualified);
            return "<" + qualified + ">";
        };
        var target:TupleType = new TypeImpls.TupleTypeImpl([root]);
        var tail = typeName.split(".").reverse();
        while (tail.length > 0) {
            console.log("Looking for: %s", tail.join("."));
            var head = tail.pop();
            target = TypeImpls.TupleAccess.getObject(target).properties[head];
        }

        if (TypeImpls.TupleAccess.isObject(target)) {
            // custom printing of the desired object: unfolds one level, and uses standard toString for the remaining parts
            var targetObject = TypeImpls.TupleAccess.getObject(target);
            var propertyNames = Object.keys(targetObject.properties).sort();
            propertyNames.forEach(p => {
                var propertyType = targetObject.properties[p];
                console.log("\t%s.%s: %s", typeName, p, TypeImpls.toPrettyString(propertyType, ()=>"{...}"));
                var isObject = TypeImpls.TupleAccess.isObject(propertyType);
                if (isObject) {
                    var objectType = TypeImpls.TupleAccess.getObject(propertyType);
                    var isInvokedFunction = TypeImpls.TupleAccess.isFunction(propertyType);
                    var constructorProperty:TupleType = objectType.properties["c" + /* silly typescript, this is a map */"onstructor"];
                    var isUninvokedFunction = !isInvokedFunction && TypeImpls.TupleAccess.isObject(constructorProperty) && (canonicalNamer(TypeImpls.TupleAccess.getObject(constructorProperty)) === "<Function>");
                    if (isUninvokedFunction) {
                        console.log("\t\tUninvoked...");
                    } else if (isInvokedFunction) {
                        var functionType = TypeImpls.TupleAccess.getFunction(propertyType);
                        var unwrappedFunctionTypes:FunctionType[] = [];
                        if (functionType.functionKind === TypeImpls.FunctionKinds.Intersection) {
                            unwrappedFunctionTypes = (<IntersectionFunctionType>functionType).members;
                        } else {
                            unwrappedFunctionTypes = [functionType];
                        }
                        unwrappedFunctionTypes.forEach(f =>
                                console.log("\t\t%s", TypeImpls.functionToPrettyString(f, canonicalNamer))
                        );
                    } else {
                        Object.keys(objectType.properties).sort().forEach(p =>
                                console.log("\t\t%s: %s", p, TypeImpls.toPrettyString(objectType.properties[p], canonicalNamer))
                        );
                    }

                }
            });
        } else {
            console.log(TypeImpls.toPrettyString(target));
        }
        done();
    } catch (e) {
        done(e);
        throw e;
    }
}


function testFile(file:string, rootIdentifier:string, inferencerConfig:InferencerConfig, done:Function, flowConfig:PrecisionConfig) {
    TraceMaker.getTraceFromSourceFile(file, function (err:any, trace:Trace) {
        testTrace(err, trace, rootIdentifier, inferencerConfig, done, flowConfig);
    });
}

describe("InferredTypeInspectorTests", function () {
    var config = inferenceConfigs.fullIntersection;
    var flowConfig = {}; // empty

    this.timeout(30 * 1000);
    it('Should show reasonable types for undercore.js', function (done) {
        testFile("fixtures/underscore-singlefile.js", "_.prototype", config, done, flowConfig);
    });
});