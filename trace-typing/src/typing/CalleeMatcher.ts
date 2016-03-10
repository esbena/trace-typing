import * as TypeImpls from "./TypeImpls";
import * as GenericFunctionTypeInferencer from "./GenericFunctionTypeInferencer";
import * as Misc from "../Misc";

export function getInputs(calleeTmp:Variable, baseTmp:Variable, argsTmps:Variable[], lattice:CompleteLattice<TupleType>, variables:Variables<TupleType>, inferredEnv:Variables<TupleType>) {
    var base:TupleType = variables.read(baseTmp);
    var calleeTupleType = variables.read(calleeTmp);
    var callee:FunctionType;
    if (TypeImpls.TupleAccess.isFunction(calleeTupleType)) {
        callee = TypeImpls.TupleAccess.getFunction(calleeTupleType);
    } else {
        callee = TypeImpls.constants.FunctionBottom;
    }
    var args:TupleType[] = argsTmps.map(argTmp => {
        var arg = variables.read(argTmp);
        // FIXME introduce TypeError for this?
        // We do not allow under approximations for finding matching function signatures
        arg = lattice.lub(arg, inferredEnv.read(argTmp));
        return arg;
    });
    return {
        callee: callee,
        base: base,
        args: args
    }
}

function attemptInstantiation(instantiable:TupleType, instantiation:TupleType) {
    var instantiated:TupleType = instantiable;
    if (isTypeParameter(instantiable)) {
        instantiated = instantiation;
    } else {
        if (TypeImpls.TupleAccess.isObject(instantiable) && TypeImpls.TupleAccess.isObject(instantiation)) {
            var instantiableObject = TypeImpls.TupleAccess.getObject(instantiable);
            var instantiableProperties = instantiableObject.properties;
            for (var propertyName in instantiableProperties) {
                var instantiatedProperty = TypeImpls.TupleAccess.getObject(instantiation).properties[propertyName];
                if (isTypeParameter(instantiableProperties[propertyName]) && instantiatedProperty !== undefined) {
                    // instantiate as much as possible
                    instantiated = GenericFunctionTypeInferencer.substituteProperty(instantiated, propertyName, instantiatedProperty);
                }
            }
        }
    }
    return instantiated;
}
var isTypeParameter = TypeImpls.TupleAccess.isTypeParameter;
function callMatchesTypeParameterSignature(callee:SingleFunctionType, base:TupleType, args:TupleType[], isAssignmentCompatible:(to:TupleType, from:TupleType)=>boolean, isConstructorCall:boolean):boolean {
    var instantiatedBase:TupleType = attemptInstantiation(callee.base, base);
    if (!isAssignmentCompatible(instantiatedBase, base)) {
        return false;
    }

    for (var i = 0; i < Math.min(callee.args.length, args.length); i++) {
        var instantiatedArg:TupleType = attemptInstantiation(callee.args[i], args[i]);
        if (!isAssignmentCompatible(instantiatedArg, args[i])) {
            return false;
        }
    }
    return true;
}
function callMatchesSignature(callee:SingleFunctionType, base:TupleType, args:TupleType[], isAssignmentCompatible:(to:TupleType, from:TupleType)=>boolean, isConstructorCall:boolean) {
    var baseMatch = isAssignmentCompatible(callee.base, base);
    if (!isConstructorCall && !baseMatch) {
        return false;
    }
    if (callee.args.length !== args.length) {
        return false; // XXX rethink the strictness of this check
    }
    for (var i = 0; i < args.length; i++) {
        var arg = args[i];
        var potentialMatchedArg = callee.args[i];
        if (!isAssignmentCompatible(potentialMatchedArg, arg)) {
            return false;
        }
    }
    return true;
}
export function match(callee:FunctionType, base:TupleType, args:TupleType[], isAssignmentCompatible:(to:TupleType, from:TupleType) => boolean, isConstructorCall:boolean):{matches: SingleFunctionType[], isTop: boolean} {
    var potentialMatches:SingleFunctionType[];
    switch (callee.functionKind) {
        case TypeImpls.FunctionKinds.Single:
            potentialMatches = [<SingleFunctionType>callee];
            break;
        case TypeImpls.FunctionKinds.Intersection:
            potentialMatches = ((<IntersectionFunctionType>callee).members).slice();
            break;
        case TypeImpls.FunctionKinds.Top:
            return {matches: [], isTop: true};
        case TypeImpls.FunctionKinds.Bottom:
            potentialMatches = [];
            break;
        default:
            throw new Error("Unhandled kind: " + callee.functionKind);
    }

    var matches = potentialMatches.filter(potentialMatch => callMatchesSignature(potentialMatch, base, args, isAssignmentCompatible, isConstructorCall));
    if (false && matches.length === 0 && potentialMatches.length === 1) {
        if (callMatchesTypeParameterSignature(potentialMatches[0], base, args, isAssignmentCompatible, isConstructorCall)) {
            matches = [potentialMatches[0]];
        }
    }

    var DEBUG = false;
    if (DEBUG) {
        console.log("%s called with (%s) @ %s", TypeImpls.functionToPrettyString(callee), args.map(arg => TypeImpls.toPrettyString(arg)).join(", "), TypeImpls.toPrettyString(base));
        if (matches.length === 0) {
            console.log("NO MATCH");
        } else {
            console.log("=> %s", matches.map(match => TypeImpls.functionToPrettyString(match)).join(", "));
        }
    }

    return {matches: matches, isTop: false};
}
