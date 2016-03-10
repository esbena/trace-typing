/* 
 * Copyright 2015 Samsung Research America, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
///<reference path="../types.d.ts"/>
import * as Misc from '../Misc';
import * as AST from '../TraceLanguageAST';
import * as SJS from '../SJS';
import {ObjectClassification} from '../SJSObjectClassification';

var DEBUG = false;

interface NumberType extends Type {
    numberKind: NumberKinds
}
interface StringType extends Type {
    stringKind: StringKinds
}
interface BooleanType extends Type {
    booleanKind: BooleanKinds
}
interface UndefinedType extends Type {
    undefinedKind: UndefinedKinds
}
interface NullType extends Type {
    nullKind: NullKinds
}
export class ObjectTypeImpl implements ObjectType {
    public typeKind = TypeKinds.Object;
    public objectKind = ObjectKinds.Some;
    public MRO:Map<string, TupleType> = undefined;
    public MRW:Map<string, TupleType> = undefined;
    public isAbstract:boolean = false;

    constructor(public properties:PropertyTypes, public functionType:FunctionType, public objectClassification:ObjectClassificationType, public readOnlyPropertyNames:Set<string>) {
        if (DEBUG) {
            for (var p in properties) {
                if (!readOnlyPropertyNames.has(p)) {
                    throw new Error("Non-existent read-only property: " + p);
                }
            }
        }
        if (functionType === undefined) {
            throw new Error("Undef function");
        }

        //console.log("New object: {%s}", Object.keys(properties).sort().join(","));
    }
}

export class RecursiveTupleTypeManager {
    private static map:Map<number, TupleType[]>;
    private static nextId = 0;

    public static reset() {
        RecursiveTupleTypeManager.nextId = 0;
        RecursiveTupleTypeManager.map = new Map<number, TupleType[]>();
    }

    public static prepare():number {
        var id = RecursiveTupleTypeManager.nextId++;
        if (RecursiveTupleTypeManager.map.has(id)) {
            throw new Error("Id " + id + "already exists?!");
        }
        RecursiveTupleTypeManager.map.set(id, []);
        return id;
    }

    public static register(tuple:TupleType, ids:number[]) {
        ids.forEach(id => {
            RecursiveTupleTypeManager.checkExists(id);
            RecursiveTupleTypeManager.map.get(id).push(tuple);
        });
    }

    public static replace(id:number, objectType:ObjectType, lub:MergeOperator<TupleType>) {
        RecursiveTupleTypeManager.checkExists(id);
        // replace all references, in a fixpoint
        while (RecursiveTupleTypeManager.map.get(id).length > 0) {
            var tuplesToUpdate = RecursiveTupleTypeManager.map.get(id).slice();
            RecursiveTupleTypeManager.map.get(id).length = 0; // clear content
            tuplesToUpdate.forEach(tupleToUpdate => {
                TupleAccess.removeRecursiveReferenceID(tupleToUpdate, id);
                var mergedObjectType:ObjectType;
                if (TupleAccess.isObject(tupleToUpdate)) {
                    var recursiveObjectTuple = new TupleTypeImpl([objectType]);
                    mergedObjectType = TupleAccess.getObject(lub(tupleToUpdate, recursiveObjectTuple));
                } else {
                    mergedObjectType = objectType;
                }
                TupleAccess.setObject(tupleToUpdate, mergedObjectType);
                // console.log("Resolved recursive to %s", toPrettyString(tupleToUpdate));
            });
        }
        RecursiveTupleTypeManager.map.delete(id);
    }

    private static checkExists(id:number) {
        if (!RecursiveTupleTypeManager.map.has(id)) {
            throw new Error("Id " + id + "does not exist?!");
        }
    }
}
export class ObjectClassificationTypeImpl implements ObjectClassificationType {
    constructor(public classifications:Set<ObjectClassification>) {
    }
}
export class TypeParameterImpl implements TypeParameter {
    public typeKind = TypeKinds.TypeParameter;

    constructor(public name:string) {
    }
}
export class TupleTypeImpl implements TupleType {
    public elements:Type[];


    constructor(elements:Type[], normalizeForConstants = true) {
        if (normalizeForConstants && elements.length === 1) {
            var element = elements[0];
            switch (element) {
                case constants.BooleanTop:
                    return convenienceConstants.BooleanTop;
                case constants.NullTop:
                    return convenienceConstants.NullTop;
                case constants.NumberTop:
                    return convenienceConstants.NumberTop;
                case constants.UndefinedTop:
                    return convenienceConstants.UndefinedTop;
                case constants.ObjectTop:
                    return convenienceConstants.ObjectTop;
                case constants.RecursiveReferenceTop:
                    return convenienceConstants.RecursiveReferenceTop;
                case constants.ObjectTopDueToRecursionTop:
                    return convenienceConstants.ObjectTopDueToRecursionTop;
                case constants.TypeParameterTop:
                    return convenienceConstants.TypeParameterTop;
            }
        }
        this.elements = this.makeElementOrder(elements);
        if(elements === constants.Bottom.elements){
            return <TupleTypeImpl>(constants.Bottom);
        }
        if (TupleAccess.isRecursiveReference(this)) {
            var recursiveReferenceType = TupleAccess.getRecursiveReference(this);
            if (recursiveReferenceType.recursiveReferenceKind === RecursiveReferenceKinds.Some) {
                RecursiveTupleTypeManager.register(this, recursiveReferenceType.ids);
            }
        }
    }

    private makeElementOrder(ts:Type[]) {
        var elements = constants.Bottom.elements;
        if (DEBUG) {
            var usedKinds = new Set<TypeKinds>();
        }
        for (var i = 0; i < ts.length; i++) {
            var t = ts[i];
            var kind = t.typeKind;
            if (DEBUG) {
                if (usedKinds.has(kind)) {
                    throw new Error("Duplicate type kind: " + kind);
                }
                usedKinds.add(kind);
            }
            if(elements === constants.Bottom.elements){
               elements = constants.Bottom.elements.slice()
            }
            elements[kind] = t;
        }
        return elements;
    }
}

export var TupleAccess = {
    isObject(tuple:TupleType) {
        return tuple.elements[TypeKinds.Object] !== constants.ObjectBottom;
    },
    isFunction(tuple:TupleType) {
        var isObject = this.isObject(tuple);
        if (!isObject) {
            return false;
        }
        var object = this.getObject(tuple);
        return object.functionType !== constants.FunctionBottom;
    },
    getFunction(tuple:TupleType): FunctionType {
        if (!this.isFunction(tuple)) {
            throw new Error("Tuple does is not a function");
        }
        return this.getObject(tuple).functionType;
    },
    isUndefined(tuple:TupleType) {
        return tuple.elements[TypeKinds.Undefined] !== constants.UndefinedBottom;
    },
    isNull(tuple:TupleType) {
        return tuple.elements[TypeKinds.Null] !== constants.NullBottom;
    },
    isString(tuple:TupleType) {
        return tuple.elements[TypeKinds.String] !== constants.StringBottom;
    },
    isNumber(tuple:TupleType) {
        return tuple.elements[TypeKinds.Number] !== constants.NumberBottom;
    },
    isBoolean(tuple:TupleType) {
        return tuple.elements[TypeKinds.Boolean] !== constants.BooleanBottom;
    },
    getObject(tuple:TupleType): ObjectType {
        if (!this.isObject(tuple)) {
            throw new Error("Tuple does not have an object: " + toPrettyString(tuple));
        }
        return <ObjectType>tuple.elements[TypeKinds.Object];
    },
    setObject(tuple:TupleType, object:Type): void {
        tuple.elements[TypeKinds.Object] = object;
    },
    isRecursiveReference(tuple:TupleType) {
        return tuple.elements[TypeKinds.RecursiveReference] !== constants.RecursiveReferenceBottom;
    },
    getRecursiveReference(tuple:TupleType): RecursiveReferenceType {
        if (!this.isRecursiveReference(tuple)) {
            throw new Error("Tuple does not have a recursive reference");
        }
        return <RecursiveReferenceType>tuple.elements[TypeKinds.RecursiveReference];
    },
    setBottomRecursiveReference(tuple:TupleType): void {
        tuple.elements[TypeKinds.RecursiveReference] = constants.RecursiveReferenceBottom;
    },
    isNullOrUndefined(type:TupleType) {
        return this.isUndefined(type) || this.isNull(type);
    },
    isObjectTopDueToRecursion(type:TupleType) {
        return type.elements[TypeKinds.ObjectTopDueToRecursion] === constants.ObjectTopDueToRecursionTop;
    },
    setObjectTopDueToRecursion(type:TupleType) {
        type.elements[TypeKinds.Object] = constants.ObjectTop;
        type.elements[TypeKinds.ObjectTopDueToRecursion] = constants.ObjectTopDueToRecursionTop;
    },
    removeRecursiveReferenceID(type:TupleType, toRemove:number) {
        if (this.isRecursiveReference(type)) {
            var ids = (<RecursiveReferenceType>(type.elements[TypeKinds.RecursiveReference])).ids.filter(id => id !== toRemove);

            var modified:RecursiveReferenceType;
            if (ids.length === 0) {
                modified = constants.RecursiveReferenceBottom;
            } else {
                modified = new RecursiveReferenceTypeImpl(ids);
            }
            type.elements[TypeKinds.RecursiveReference] = modified;
        }
    },
    makeWithoutUndefined(type:TupleType){
        var copy = new TupleTypeImpl(type.elements);
        copy.elements[TypeKinds.Undefined] = constants.UndefinedBottom;
        return copy;
    },
    isTypeParameter(type:TupleType): boolean{
        return type.elements[TypeKinds.TypeParameter] !== constants.TypeParameterBottom;
    },
    getTypeParameter(type:TupleType): TypeParameter{
        return <TypeParameter>type.elements[TypeKinds.TypeParameter];
    }
};
export class SingleFunctionTypeImpl implements SingleFunctionType {
    public functionKind = FunctionKinds.Single;

    constructor(public base:TupleType, public args:TupleType[], public result:TupleType, public callKinds:Set<CallKinds>) {
    }
}
export class IntersectionFunctionTypeImpl implements IntersectionFunctionType {
    public functionKind = FunctionKinds.Intersection;
    public members:SingleFunctionType[];

    constructor(members:SingleFunctionType[]) {
        this.members = members.slice();
    }
}

export class RecursiveReferenceTypeImpl implements RecursiveReferenceType {
    public typeKind = TypeKinds.RecursiveReference;
    public recursiveReferenceKind = RecursiveReferenceKinds.Some;

    constructor(public ids:number[]) {
    }
}
export class ObjectTopDueToRecursionTypeImpl implements ObjectTopDueToRecursionType {
    public typeKind = TypeKinds.ObjectTopDueToRecursion;

    constructor(public objectTopDueToRecursionKind:ObjectTopDueToRecursionKinds) {
    }
}
export enum TypeKinds{
    /*0*/Object,
/*1*/Null,
/*2*/String,
/*3*/Number,
/*4*/Boolean,
/*5*/Undefined,
/*6*/RecursiveReference,
/*7*/ObjectTopDueToRecursion,
/*8*/TypeParameter
}
export enum ObjectTopDueToRecursionKinds {
    Bottom, Top
}
export enum ObjectKinds {
    Bottom, Some, Top
}
enum NullKinds {
    Bottom, Top
}
enum StringKinds {
    Bottom, Top
}
enum NumberKinds {
    Bottom, Top
}
enum BooleanKinds {
    Bottom, Top
}
enum UndefinedKinds {
    Bottom, Top
}
enum RecursiveReferenceKinds {
    Bottom, Some, Top
}
export enum FunctionKinds {
    Bottom, Intersection, Single, Top
}
export enum CallKinds {
    Constructor, Function, Method
}

export function mapPrimitiveKindToType(kind:AST.PrimitiveKind):Type {
    switch (kind) {
        case AST.PrimitiveKind.Number:
            return constants.NumberTop;
        case AST.PrimitiveKind.String:
            return constants.StringTop;
        case AST.PrimitiveKind.Boolean:
            return constants.BooleanTop;
        case AST.PrimitiveKind.Undefined:
            return constants.UndefinedTop;
        case AST.PrimitiveKind.Null:
            return constants.NullTop;
        default:
            throw new Error("Unhandled primitive kind: " + kind);
    }
}

var recursiveIDs:WeakMap<TupleType, string>;
var nextRecursiveID:number;
var stringCache:WeakMap<Type, string>;
function initialize() {
    recursiveIDs = new WeakMap<TupleType, string>();
    stringCache = new WeakMap<Type, string>();
    nextRecursiveID = 0;
}
var BOT_SYMBOL = '⊥';
var TOP_SYMBOL = '⊤';
var ignoredPropertyNames = ["toString",
    "apply",
    "call",
    "bind",
    "name",
    "hasOwnProperty",
    "getOwnPropertyNames",
    "__defineGetter__",
    "__defineSetter__",
    "__lookupGetter__",
    "__lookupSetter__",
    "constructor",
    "hasOwnProperty",
    "isPrototypeOf",
    "length",
    "propertyIsEnumerable",
    "toLocaleString",
    "toString",
    "valueOf"];

initialize();
export function toPrettyString(type:TupleType, canonicalNamer?:(o:ObjectType) => string, forTest?:boolean, depth:number = 0):string {
    if (forTest) {
        initialize();
    }
    function getRecursiveID(rec:TupleType):string {
        if (!recursiveIDs.has(rec)) {
            recursiveIDs.set(rec, "Type" + nextRecursiveID++);
        }
        return recursiveIDs.get(rec);
    }

    var onStack = new Set<TupleType>();
    return tupleToPrettyString(type, canonicalNamer, forTest, depth);


    function tupleToPrettyString(tuple:TupleType, canonicalNamer?:(o:ObjectType) => string, forTest?:boolean, depth:number = 0):string {
        if (onStack.has(tuple)) {
            return getRecursiveID(tuple)
        }
        onStack.add(tuple);
        var res = "";

        if (tuple === constants.Top) {
            res = TOP_SYMBOL;
        } else if (tuple === constants.Bottom) {
            res = BOT_SYMBOL;
        } else {
            var strings = tuple.elements.filter(type => {
                return type !== constants.ObjectBottom &&
                    type !== constants.RecursiveReferenceBottom &&
                    type !== constants.StringBottom &&
                    type !== constants.NumberBottom &&
                    type !== constants.BooleanBottom &&
                    type !== constants.UndefinedBottom &&
                    type !== constants.NullBottom &&
                    type !== constants.ObjectTopDueToRecursionBottom &&
                    type !== constants.TypeParameterBottom;
            }).map(e => toPrettyStringInner(e, forTest, depth));
            switch (strings.length) {
                case 0:
                    res = BOT_SYMBOL;
                    break;
                case 1:
                    res = strings[0];
                    break;
                default:
                    res = "(" + strings.join(",") + ")";
                    break;
            }
        }

        if (recursiveIDs.has(tuple)) {
            res += " as " + getRecursiveID(tuple);
        }
        onStack.delete(tuple);
        return res;
    }

    function toPrettyStringInner(type:Type, forTest?:boolean, depth:number = 0):string {
        if (!forTest && depth > 2 && type.typeKind === TypeKinds.Object) {
            return "...";
        }
        if (!canonicalNamer && stringCache.has(type)) {
            return stringCache.get(type);
        }
        function objectToPrettyString(o:ObjectType):string {
            function getShortName() {
                function hasManyGlobalProperties() {
                    return ['Math', 'Function', 'Object', 'JSON', 'Number', 'String', 'RegExp', 'Error', 'Boolean', 'isNaN', 'eval'].every(p => p in o.properties);
                }

                function hasManyArrayProperties() {
                    return ['pop', 'push', 'forEach', 'filter', 'slice', 'map'].every(p => p in o.properties);
                }

                if (hasManyGlobalProperties()) {
                    return "~global";
                }
                if (Misc.getAbstractArrayFieldName() in o.properties && hasManyArrayProperties) {
                    return "~Array<" + tupleToPrettyString(o.properties[Misc.getAbstractArrayFieldName()], canonicalNamer, forTest, depth + 1) + ">";
                }
            }

            var canonicalName = canonicalNamer && canonicalNamer(o);
            if (canonicalName !== undefined) {
                return canonicalName;
            }
            var res = "";
            var shortName = getShortName();
            if (shortName) {
                res = shortName;
            } else if (o.functionType.functionKind !== FunctionKinds.Bottom && o.functionType.functionKind !== FunctionKinds.Top) {
                res += "<";
                res += functionToPrettyString(o.functionType, canonicalNamer, tupleToPrettyString, forTest, depth);
                res += ">"
            } else {
                res = "{";
                var first = true;
                var propertyNames = Object.getOwnPropertyNames(o.properties).sort();
                if (!forTest)
                    propertyNames = propertyNames.filter(n => ignoredPropertyNames.indexOf(n) === -1);
                if (propertyNames.length > 10 && !forTest) {
                    res += propertyNames.join(", ");
                } else {
                    for (var i in propertyNames) {
                        var p = propertyNames[i];
                        var t = o.properties[p];
                        if (!first) {
                            res += ", "
                        }
                        first = false;
                        res += p + ": " + tupleToPrettyString(t, canonicalNamer, forTest, depth + 1);
                    }
                }
                res += "}";
            }
            return res;
        }

        var result:string = TypeKinds[type.typeKind];
        /* default */
        // TODO add bottom/top check
        switch (type.typeKind) {
            case TypeKinds.Object:
                if (type === constants.ObjectBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.ObjectTop) {
                    result += "_" + TOP_SYMBOL;
                } else {
                    result = objectToPrettyString(<ObjectType>type);
                }
                break;
            case TypeKinds.RecursiveReference:
                if (type === constants.RecursiveReferenceBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.RecursiveReferenceTop) {
                    result += "_" + TOP_SYMBOL;
                } else {
                    result += '(' + (<RecursiveReferenceType>type).ids.join(', ') + ')';
                }
                break;
            case TypeKinds.String:
                if (type === constants.StringBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.StringTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.Number:
                if (type === constants.NumberBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.NumberTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.Boolean:
                if (type === constants.BooleanBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.BooleanTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.Undefined:
                if (type === constants.UndefinedBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.UndefinedTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.Null:
                if (type === constants.NullBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.NullTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.ObjectTopDueToRecursion:
                if (type === constants.ObjectTopDueToRecursionBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.ObjectTopDueToRecursionTop) {
                    result += "_" + TOP_SYMBOL;
                }
                break;
            case TypeKinds.TypeParameter:
                if (type === constants.TypeParameterBottom) {
                    result += "_" + BOT_SYMBOL;
                } else if (type === constants.TypeParameterTop) {
                    result += "_" + TOP_SYMBOL;
                } else {
                    result /*+*/ = (<TypeParameter>type).name;
                }

                break;
            default:
                throw new Error("Unhandled type kind: " + type.typeKind);
        }
        if (!canonicalNamer) {
            stringCache.set(type, result);
        }
        return result;
    }
}

export function functionToPrettyString(f:FunctionType, canonicalNamer?:(o:ObjectType) => string, typeToPrettyString:(type:TupleType, canonicalNamer:(o:ObjectType) => string, forTest:boolean, depth:number)=>string = toPrettyString, forTest?:boolean, depth:number = 0):string {
    switch (f.functionKind) {
        case FunctionKinds.Bottom:
            return BOT_SYMBOL + " -> " + BOT_SYMBOL;
        case FunctionKinds.Top:
            return TOP_SYMBOL + " -> " + TOP_SYMBOL;
        case FunctionKinds.Single:
            return ((f:SingleFunctionType) => {
                var res = "(";
                var first = true;
                f.args.forEach(t => {
                    if (!first) {
                        res += ", "
                    }
                    first = false;
                    res += typeToPrettyString(t, canonicalNamer, forTest, depth + 1)
                });
                res += ") -> " + typeToPrettyString(f.result, canonicalNamer, forTest, depth + 1);
                res += " @ " + typeToPrettyString(f.base, canonicalNamer, forTest, depth + 1);
                return res;
            })(<SingleFunctionType>f);
        case FunctionKinds.Intersection:
            return ((f:IntersectionFunctionType) => {
                var res = "I(";
                if (f.members.length > 1 && !forTest) {
                    res += "x" + f.members.length;
                } else {
                    var first = true;
                    f.members.forEach(t => {
                        if (!first) {
                            res += ", "
                        }
                        first = false;
                        res += functionToPrettyString(t, canonicalNamer, typeToPrettyString, forTest, depth);
                    });
                }
                res += ")";
                return res;
            })(<IntersectionFunctionType>f);
        default:
            throw new Error("Unhandled enum: " + f.functionKind);
    }
}

export var constants = (function () {
    var numberTop:NumberType = {typeKind: TypeKinds.Number, numberKind: NumberKinds.Top};
    var numberBottom:NumberType = {typeKind: TypeKinds.Number, numberKind: NumberKinds.Bottom};
    var stringTop:StringType = {typeKind: TypeKinds.String, stringKind: StringKinds.Top};
    var stringBottom:StringType = {typeKind: TypeKinds.String, stringKind: StringKinds.Bottom};
    var booleanTop:BooleanType = {typeKind: TypeKinds.Boolean, booleanKind: BooleanKinds.Top};
    var booleanBottom:BooleanType = {typeKind: TypeKinds.Boolean, booleanKind: BooleanKinds.Bottom};
    var undefinedTop:UndefinedType = {typeKind: TypeKinds.Undefined, undefinedKind: UndefinedKinds.Top};
    var undefinedBottom:UndefinedType = {typeKind: TypeKinds.Undefined, undefinedKind: UndefinedKinds.Bottom};
    var nullTop:NullType = {typeKind: TypeKinds.Null, nullKind: NullKinds.Top};
    var nullBottom:NullType = {typeKind: TypeKinds.Null, nullKind: NullKinds.Bottom};

    var functionTop:FunctionType = {functionKind: FunctionKinds.Top};
    var functionBottom:FunctionType = {functionKind: FunctionKinds.Bottom};
    var recursiveReferenceTop:RecursiveReferenceType = {
        typeKind: TypeKinds.RecursiveReference,
        recursiveReferenceKind: RecursiveReferenceKinds.Top
    };
    var recursiveReferenceBottom:RecursiveReferenceType = {
        typeKind: TypeKinds.RecursiveReference,
        recursiveReferenceKind: RecursiveReferenceKinds.Bottom
    };

    var objectTopDueToRecursionTop = new ObjectTopDueToRecursionTypeImpl(ObjectTopDueToRecursionKinds.Top);
    var objectTopDueToRecursionBottom = new ObjectTopDueToRecursionTypeImpl(ObjectTopDueToRecursionKinds.Bottom);

    var typeParameterBottom = new TypeParameterImpl("_");
    var typeParameterTop = new TypeParameterImpl("?");

    var topObjectClassification = new ObjectClassificationTypeImpl(new Set<ObjectClassification>());
    topObjectClassification.classifications.add(ObjectClassification.Object);
    topObjectClassification.classifications.add(ObjectClassification.Array);
    topObjectClassification.classifications.add(ObjectClassification.Map);

    var objectTop:ObjectType = {
        typeKind: TypeKinds.Object,
        objectKind: ObjectKinds.Top,
        properties: Object.create(null),
        functionType: functionTop,
        objectClassification: topObjectClassification,
        readOnlyPropertyNames: new Set<string>(),
        MRO: undefined,
        MRW: undefined,
        isAbstract: undefined
    };
    var objectBottom:ObjectType = {
        typeKind: TypeKinds.Object,
        objectKind: ObjectKinds.Bottom,
        properties: undefined,
        functionType: functionBottom,
        objectClassification: new ObjectClassificationTypeImpl(new Set<ObjectClassification>()),
        readOnlyPropertyNames: undefined,
        MRO: undefined,
        MRW: undefined,
        isAbstract: undefined
    };

    var bottoms:Type[] = [numberBottom, stringBottom, booleanBottom, undefinedBottom, nullBottom, recursiveReferenceBottom, objectBottom, objectTopDueToRecursionBottom, typeParameterBottom];
    var tops:Type[] = [numberTop, stringTop, booleanTop, undefinedTop, nullTop, recursiveReferenceTop, objectTop, objectTopDueToRecursionBottom /* !!! */, typeParameterTop];
    var bottom:TupleType = {elements: bottoms};
    var top:TupleType = {elements: tops};

    // order important for tuple types!
    bottom.elements.sort((t1:Type, t2:Type) => t1.typeKind - t2.typeKind);
    top.elements.sort((t1:Type, t2:Type) => t1.typeKind - t2.typeKind);

    return {
        Top: top,
        Bottom: bottom,
        bottomTypes: bottoms,
        NumberTop: numberTop,
        NumberBottom: numberBottom,
        StringTop: stringTop,
        StringBottom: stringBottom,
        BooleanTop: booleanTop,
        BooleanBottom: booleanBottom,
        UndefinedTop: undefinedTop,
        UndefinedBottom: undefinedBottom,
        NullTop: nullTop,
        NullBottom: nullBottom,
        ObjectTop: objectTop,
        ObjectBottom: objectBottom,
        FunctionTop: functionTop,
        FunctionBottom: functionBottom,
        RecursiveReferenceTop: recursiveReferenceTop,
        RecursiveReferenceBottom: recursiveReferenceBottom,
        ObjectTopDueToRecursionTop: objectTopDueToRecursionTop,
        ObjectTopDueToRecursionBottom: objectTopDueToRecursionBottom,
        TypeParameterTop: typeParameterTop,
        TypeParameterBottom: typeParameterBottom
    }
})();

export var convenienceConstants = (function () {
    return {
        UndefinedTop: new TupleTypeImpl([constants.UndefinedTop], false),
        NullTop: new TupleTypeImpl([constants.NullTop], false),
        BooleanTop: new TupleTypeImpl([constants.BooleanTop], false),
        StringTop: new TupleTypeImpl([constants.StringTop], false),
        NumberTop: new TupleTypeImpl([constants.NumberTop], false),
        ObjectTop: new TupleTypeImpl([constants.ObjectTop], false),
        RecursiveReferenceTop: new TupleTypeImpl([constants.RecursiveReferenceTop], false),
        ObjectTopDueToRecursionTop: new TupleTypeImpl([constants.ObjectTopDueToRecursionTop], false),
        TypeParameterTop: new TupleTypeImpl([constants.TypeParameterTop], false)
    }
})();

var c = 0;

// type compatibility hack
interface forEachable<T> {
    forEach: (callbackfn:(value:T) => void, thisArg?:any) => void
}
var showStringCollectionDiff = function (s1:forEachable<string>, s2:forEachable<string>) {
    var diff1 = new Set<string>();
    var diff2 = new Set<string>();

    s1.forEach(n => diff1.add(n));
    s2.forEach(n => diff1.delete(n));
    s2.forEach(n => diff2.add(n));
    s1.forEach(n => diff2.delete(n));

    var diff1array:string[] = [];
    var diff2array:string[] = [];
    diff1.forEach(n => diff1array.push(n));
    diff2.forEach(n => diff2array.push(n));
    console.log("Diffs:");
    console.log("   s1 - s2 = {%s}", diff1array.sort());
    console.log("   s2 - s1 = {%s}", diff2array.sort());
};
export function isObjectTypeEqual(t1:ObjectType, t2:ObjectType, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (recursionGuard === undefined) {
        //console.log("New recursionGuard...");
        recursionGuard = new Map<ObjectType,Set<ObjectType>>();
        c++;
        if (c > 10000) {
            //throw new Error("Gimme the stack");
        }
    }
    if (t1 === t2) {
        return true;
    }
    if (t1.objectKind !== t2.objectKind) {
        if (debug) {
            console.log("Found inequality at objectKind: %s vs %s", ObjectKinds[t1.objectKind], ObjectKinds[t2.objectKind]);
        }
        return false;
    }
    switch (t1.objectKind) {
        case ObjectKinds.Bottom:
        case ObjectKinds.Top:
            return true;
        case ObjectKinds.Some:
            break;
        default:
            throw new Error("Unhandled kind: " + t1.typeKind);
    }

    var t1propertyNames = Object.keys(t1.properties);
    var t2propertyNames = Object.keys(t2.properties);
    var samePropertyNames = t1propertyNames.length === t2propertyNames.length && Misc.isSetFlatEqual(Misc.toSet(t1propertyNames), Misc.toSet(t2propertyNames));
    if (!samePropertyNames) {
        if (debug) {
            console.log("Found inequality at property names: %d vs %d", t1propertyNames.length, t2propertyNames.length);
            showStringCollectionDiff(t1propertyNames, t2propertyNames);
        }
        // assumes no Bottom-typed properties
        return false;
    }

    var t1fk = t1.functionType.functionKind;
    var t2fk = t2.functionType.functionKind;
    if(t1fk !== t2fk && (t1fk === FunctionKinds.Bottom || t1fk === FunctionKinds.Top || t2fk === FunctionKinds.Bottom || t2fk === FunctionKinds.Top)){
        // extra check for some speedup, strictly not needed
        return false;
    }

    if (!recursionGuard.has(t1)) {
        recursionGuard.set(t1, new Set<ObjectType>());
    }
    if (recursionGuard.get(t1).has(t2)) {
        return true;
    }
    recursionGuard.get(t1).add(t2);

    if (!isFunctionTypeEqual(t1.functionType, t2.functionType, debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment)) {
        if (debug)
            console.log("Found inequality at property function types");
        return false;
    }
    if (!isObjectClassificationTypeEqual(t1.objectClassification, t2.objectClassification)) {
        if (debug)
            console.log("Found inequality at object classification type");
        return false;
    }

    var ro1 = t1.readOnlyPropertyNames;
    var ro2 = t2.readOnlyPropertyNames;
    if (!Misc.isSetFlatEqual(ro1, ro2)) {
        if (debug) {
            console.log("Found inequality at readOnlyPropertyNames: ");
            showStringCollectionDiff(ro1, ro2);
        }
        return false;
    }

    for (var i = 0; i < t1propertyNames.length; i++) {
        var propertyName = t1propertyNames[i];
        var p1 = t1.properties[propertyName];
        var p2 = t2.properties[propertyName];
        if (!isTupleTypeEqual(p1, p2, debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment)) {
            if (debug)
                console.log("Found inequality at property value .%s: %s vs %s", propertyName, toPrettyString(p1), toPrettyString(p2));
            return false;
        }
    }

    if (false) {
        // TODO should enable these checks, but merges of MRO/MRW/isAbstract never happens, so this is caught by the initial identity check in practice..
        if (t1.isAbstract !== t2.isAbstract) {
            if (debug) {
                console.log("Found inequality at isAbstract: %s vs %s", t1.isAbstract, t2.isAbstract);
            }
            return false;
        }

        if (t1.MRO !== t2.MRO || t1.MRW !== t2.MRW) {
            // TODO this check ought to be structural,
            if (debug) {
                console.log("Found inequality at MRO/MRW: (%s/%s) vs (%s/%s)", t1.MRO, t1.MRW, t2.MRO, t2.MRW);
            }
            return false;
        }
    }
    recursionGuard.get(t1).delete(t2);

    if (!asInvarianceCheckWithSpecialFunctionTreatment) {
        // normalize
        t1.functionType = t2.functionType;
        t1.properties = t2.properties;
        t1.objectClassification = t2.objectClassification;
        t1.readOnlyPropertyNames = t2.readOnlyPropertyNames;
    }
    return true;
}
export function isObjectClassificationTypeEqual(t1:ObjectClassificationType, t2:ObjectClassificationType) {
    if (t1 === t2) {
        return true;
    }
    var c1 = t1.classifications;
    var c2 = t2.classifications;

    if (!Misc.isSetFlatEqual(c1, c2)) {
        return false;
    }

    // normalize
    t1.classifications = t2.classifications;
    return true;
}
export function isFunctionTypeEqual(t1:FunctionType, t2:FunctionType, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (t1 === t2) {
        return true;
    }
    if (asInvarianceCheckWithSpecialFunctionTreatment && (t1.functionKind === FunctionKinds.Bottom || t2.functionKind === FunctionKinds.Bottom)) {
        return true;
    }
    if (t1.functionKind !== t2.functionKind) {
        if (debug) {
            console.log("Mismatch found at function kind: %s vs %s", FunctionKinds[t1.functionKind], FunctionKinds[t2.functionKind]);
        }
        return false;
    }
    switch (t1.functionKind) {
        case FunctionKinds.Bottom:
        case FunctionKinds.Top:
            return true;
        case FunctionKinds.Single:
            return isSingleFunctionTypeEqual(<SingleFunctionType>t1, <SingleFunctionType>t2, debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment);
        case FunctionKinds.Intersection:
            return isIntersectionFunctionTypeEqual(<IntersectionFunctionType>t1, <IntersectionFunctionType>t2, debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment);
        default:
            throw new Error("Unhandled kind: " + t1.functionKind);
    }
}
export function isSingleFunctionTypeEqual(t1:SingleFunctionType, t2:SingleFunctionType, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (t1 === t2) {
        return true;
    }
    if (!asInvarianceCheckWithSpecialFunctionTreatment && !isTupleTypeEqual(t1.base, t2.base, debug, recursionGuard)) {
        return false;
    }
    if (!isTupleTypeEqual(t1.result, t2.result, debug, recursionGuard)) {
        return false;
    }
    if (!isTypeArrayEqual(t1.args, t2.args, debug, recursionGuard)) {
        return false;
    }
    if (!Misc.isSetFlatEqual(t1.callKinds, t2.callKinds)) {
        return false;
    }

    // normalize
    if (!asInvarianceCheckWithSpecialFunctionTreatment) {
        t1.args = t2.args;
        t1.base = t2.base;
        t1.result = t2.result;
    }
    return true;
}
export function isIntersectionFunctionTypeEqual(t1:IntersectionFunctionType, t2:IntersectionFunctionType, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (t1 === t2) {
        return true;
    }

    if (t1.members.length !== t2.members.length) {
        return false;
    }

    // really expensive as we do not have a canonical ordering
    // TODO introduce canonical intersectiontype order?
    for (var i = 0; i < t1.members.length; i++) {
        var s1 = t1.members[i];
        var foundMatch = false;
        innerloop: for (var j = 0; j < t2.members.length; j++) {
            if (isSingleFunctionTypeEqual(s1, t2.members[j], debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment)) {
                foundMatch = true;
                break innerloop;
            }
        }
        if (!foundMatch) {
            return false;
        }
    }
    // normalize
    if (!asInvarianceCheckWithSpecialFunctionTreatment) {
        t1.members = t2.members;
    }
    return true;
}
export function isTypeArrayEqual(a1:TupleType[], a2:TupleType[], debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (a1 === a2) {
        return true;
    }
    if (a1.length !== a2.length) {
        return false;
    }
    for (var i = 0; i < a1.length; i++) {
        if (!isTupleTypeEqual(a1[i], a2[i], debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment)) {
            return false;
        }
    }
    // normalize
    if (!asInvarianceCheckWithSpecialFunctionTreatment) {
        for (var i = 0; i < a1.length; i++) {
            a1[i] = a2[i];
        }
    }
    return true;
}
export function isRecursiveReferenceTypeEqual(t1:RecursiveReferenceType, t2:RecursiveReferenceType, debug?:boolean) {
    if (t1 === t2) {
        return true;
    }
    if (t1.recursiveReferenceKind !== t2.recursiveReferenceKind) {
        return false;
    }
    switch (t1.recursiveReferenceKind) {
        case RecursiveReferenceKinds.Bottom:
        case RecursiveReferenceKinds.Top:
            return true;
        case RecursiveReferenceKinds.Some:
            if (!Misc.isArraySetFlatEqual(t1.ids, t2.ids)) {
                return false
            }
            // normalize
            t1.ids = t2.ids;

            return true;
        default:
            throw new Error("Unhandled kind: " + t1.recursiveReferenceKind);
    }
}

export function isTypeEqual(t1:Type, t2:Type, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (t1 === t2) {
        return true;
    }
    if (t1.typeKind !== t2.typeKind) {
        throw new Error("Trying to compare types of different kinds?!");
    }
    switch (t1.typeKind) {
        case TypeKinds.Object:
            return isObjectTypeEqual(<ObjectType>t1, <ObjectType>t2, debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment);
        case TypeKinds.RecursiveReference:
            return isRecursiveReferenceTypeEqual(<RecursiveReferenceType>t1, <RecursiveReferenceType>t2, debug);
        case TypeKinds.Null:
            return (<NullType>t1).nullKind === (<NullType>t2).nullKind;
        case TypeKinds.String:
            return (<StringType>t1).stringKind === (<StringType>t2).stringKind;
        case TypeKinds.Number:
            return (<NumberType>t1).numberKind === (<NumberType>t2).numberKind;
        case TypeKinds.Boolean:
            return (<BooleanType>t1).booleanKind === (<BooleanType>t2).booleanKind;
        case TypeKinds.Undefined:
            return (<UndefinedType>t1).undefinedKind === (<UndefinedType>t2).undefinedKind;
        case TypeKinds.ObjectTopDueToRecursion:
            return (<any>t1).objectTopDueToRecursionKind === (<any>t2).objectTopDueToRecursionKind;
        case TypeKinds.TypeParameter:
            return (<any>t1).name === (<any>t2).name;
        default:
            throw new Error("Unhandled kind: " + t1.typeKind);
    }
}
export function isTupleTypeEqualIgnoringFunctionReceivers(t1:TupleType, t2:TupleType, debug?:boolean) {
    return isTupleTypeEqual(t1, t2, debug, undefined, true);
}
export function isTupleTypeEqual(t1:TupleType, t2:TupleType, debug?:boolean, recursionGuard?:Map<ObjectType,Set<ObjectType>>, asInvarianceCheckWithSpecialFunctionTreatment?:boolean) {
    if (t1 === t2)
        return true;
    for (var i = 0; i < t1.elements.length; i++) {
        if (!isTypeEqual(t1.elements[i], t2.elements[i], debug, recursionGuard, asInvarianceCheckWithSpecialFunctionTreatment)) {
            if (debug) {
                console.log("Found inequality at tuple-index %d", i);
            }
            return false;
        }
    }
    // normalize
    if (!asInvarianceCheckWithSpecialFunctionTreatment) {
        t1.elements = t2.elements;
    }
    return true;
}
