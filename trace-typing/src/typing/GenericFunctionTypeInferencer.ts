///<reference path="../types.d.ts"/>
import * as TypeImpls from "./TypeImpls";
import * as Misc from "../Misc";

type TypeExtractor = (f:SingleFunctionType) => TupleType

function allEqual(types:TupleType[]):boolean {
    var target:TupleType;
    var allEqual = true;
    types.forEach(t => {
        if (target === undefined) {
            target = t;
        }
        if (!isTupleTypeEqualModuloUndefined(t, target)) {
            allEqual = false;
        }
    });
    return allEqual;
}
function isTupleTypeEqualModuloUndefined(t1:TupleType, t2:TupleType) {
    return TypeImpls.isTupleTypeEqual(TypeImpls.TupleAccess.makeWithoutUndefined(t1), TypeImpls.TupleAccess.makeWithoutUndefined(t2));
}

function extractedAllEqual(fs:SingleFunctionType[], extractor:TypeExtractor):boolean {
    return allEqual(fs.map(extractor));
}
function allEqualFunctionTypes(fs:SingleFunctionType[]) {
    var representative = fs[0];
    return fs.every(f => TypeImpls.isSingleFunctionTypeEqual(f, representative));
}
function getUnstableProperties(fs:SingleFunctionType[], extractor:TypeExtractor):Set<string> {
    var types = fs.map(extractor);
    if (types.some(t => !TypeImpls.TupleAccess.isObject(t))) {
        return new Set<string>(); // not all objects...
    }
    var objects = types.map(t => TypeImpls.TupleAccess.getObject(t));
    var allNames = new Set<string>();
    objects.forEach(o => Object.keys(o.properties).forEach(p => allNames.add(p)));

    // keep the property names where the property types vary across functions
    return Misc.toSet(Misc.toArray(allNames).filter(n =>
        objects.every(o => n in o.properties) // must agree on property names
        && !allEqual(objects.map(o => o.properties[n]))
    ));
}
export function substituteProperty(type:TupleType, name:string, to:TupleType):TupleType {
    // assumptions: type has an object with a property `name`
    var object = TypeImpls.TupleAccess.getObject(type);

    var modifiedProperties:PropertyTypes = {};
    for (var p in object.properties) { // copy all
        modifiedProperties[p] = object.properties[p];
    }
    modifiedProperties[name] = to; // modify

    // wrap
    var modifiedObject = new TypeImpls.ObjectTypeImpl(modifiedProperties, object.functionType, object.objectClassification, object.readOnlyPropertyNames);
    var modifiedType = new TypeImpls.TupleTypeImpl(type.elements);
    TypeImpls.TupleAccess.setObject(modifiedType, modifiedObject);
    return modifiedType;
}

function extractBaseType(f:SingleFunctionType):TupleType {
    return f.base;
}
function extractReturnType(f:SingleFunctionType):TupleType {
    return f.result;
}
function extractArgumentType(i:number):TypeExtractor {
    return (f:SingleFunctionType) => {
        return f.args[i];
    };
}
function extractPropertyType(objectExtractor:TypeExtractor, n:string):TypeExtractor {
    return function (f:SingleFunctionType):TupleType {
        var objectType = TypeImpls.TupleAccess.getObject(objectExtractor(f));
        return objectType.properties[n];
    }
}

export function substituteInFunctions(fs:SingleFunctionType[]):SingleFunctionType {
    if(fs.length > 100){ // XXX performance boost at cost of expressivity
        return undefined;
    }
    /**
     * Substitutes all unstable occurences of `from`-type with `to`-type in `f`.
     * Unstableness is defined by `fs`.
     *
     * Pure.
     *
     * ("all occurences" acutally means top-level occurences (base, arg, return) or a property of these.)
     */
    function substituteInFunction(f:SingleFunctionType, from:TupleType, to:TupleType, fs:SingleFunctionType[]) {
        function canSubstituteInFunction(extractor:TypeExtractor) {
            return !extractedAllEqual(fs, extractor);
        }

        function substitute(to:TupleType, extractor:TypeExtractor):TupleType {
            var substituted:TupleType;
            if (canSubstituteInFunction(extractor)) {
                if (allEqual([from, extractor(f)])) {
                    substituted = to;
                } else {
                    substituted = substituteInObject(to, extractor);
                }
            }
            return substituted;
        }


        function substituteInObject(to:TupleType, objectExtractor:TypeExtractor):TupleType {
            var unstableBasePropertyNames = Misc.toArray(getUnstableProperties(fs, objectExtractor));
            var basePropertiesCanBeSubstituted = unstableBasePropertyNames.
                map(n => extractPropertyType(objectExtractor, n)(f)).
                every(t => allEqual([from, t]))
                ;
            if (!basePropertiesCanBeSubstituted) {
                return undefined;
            }

            var propertySubsitutedBaseType:TupleType = objectExtractor(f);
            unstableBasePropertyNames.forEach(n => {
                propertySubsitutedBaseType = substituteProperty(propertySubsitutedBaseType, n, to);
            });
            return propertySubsitutedBaseType;
        }

        var base = substitute(to, extractBaseType) || f.base;
        var args = f.args.concat();
        for (var i = 0; i < Math.min.apply(undefined, fs.map(f => f.args.length)); i++) {
            args[i] = substitute(to, extractArgumentType(i)) || args[i];
        }
        var result = substitute(to, extractReturnType) || f.result;
        var callKinds = f.callKinds;

        var subst = new TypeImpls.SingleFunctionTypeImpl(base, args, result, callKinds);
        if (TypeImpls.isSingleFunctionTypeEqual(subst, f)) {
            return f;
        }
        return subst;
    }

    var topLevelExtractors:TypeExtractor[] = [];
    topLevelExtractors.push(extractBaseType);
    topLevelExtractors.push(extractReturnType);
    for (var i = 0; i < Math.min.apply(undefined, fs.map(f => f.args.length)); i++) {
        topLevelExtractors.push(extractArgumentType(i))
    }
    var propertyExtractors:TypeExtractor[] = Array.prototype.concat.apply([], topLevelExtractors.map((extractor:TypeExtractor):TypeExtractor[]=> {
        var unstablePropertyNames = Misc.toArray(getUnstableProperties(fs, extractor));
        var unstablePropertyExtractors:TypeExtractor[] = unstablePropertyNames.map(n => extractPropertyType(extractor, n));
        return unstablePropertyExtractors;
    }));


    var extractors:TypeExtractor[] = [];
    extractors = extractors.concat(topLevelExtractors);
    if(fs.length < 50) { // XXX performance boost at cost of expressivity
        extractors = extractors.concat(propertyExtractors);
    }
    extractors.reverse();
    extractors.filter(extractor => !extractedAllEqual(fs, extractor));

    var E = new TypeImpls.TupleTypeImpl([new TypeImpls.TypeParameterImpl("E")]);
    for (var i = 0; i < extractors.length; i++) {
        var substituted = fs.map(f => substituteInFunction(f, extractors[i](f), E, fs));
        if (allEqualFunctionTypes(substituted) && typeparameterUsageCount(substituted[0]) > 1) {
            return substituted[0];
        }
    }
    return undefined;
}

export function typeparameterUsageCount(f:SingleFunctionType):number {
    var typeParameterOccurences = new Map<string, number>();

    function inc(key:string) {
        if (!typeParameterOccurences.has(key)) {
            typeParameterOccurences.set(key, 0);
        }
        typeParameterOccurences.set(key, typeParameterOccurences.get(key) + 1);
    }

    function incMaybe(type:TupleType) {
        if (TypeImpls.TupleAccess.isTypeParameter(type)) {
            inc(TypeImpls.TupleAccess.getTypeParameter(type).name);
        }
    }

    var topLevelTypes:TupleType[] = [];
    topLevelTypes.push(f.base);
    topLevelTypes.push(f.result);
    for (var i = 0; i < f.args.length; i++) {
        topLevelTypes.push(f.args[i])
    }
    var propertyTypes:TupleType[] = Array.prototype.concat.apply([], topLevelTypes.
        filter(t => TypeImpls.TupleAccess.isObject(t)).
        map(t => TypeImpls.TupleAccess.getObject(t)).
        map((o:ObjectType):TupleType[]=> {
            var names = Object.keys(o.properties);
            return names.map(n => o.properties[n]);
        })
    );

    var types:TupleType[] = [];
    types = types.concat(topLevelTypes);
    types = types.concat(propertyTypes);
    types.forEach(t => incMaybe(t));

    var maxUses = 0;
    typeParameterOccurences.forEach(c => {
        if (maxUses < c) {
            maxUses = c;
        }
    });
    return maxUses;
}

