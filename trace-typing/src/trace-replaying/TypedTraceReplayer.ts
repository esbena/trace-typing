///<reference path="../types.d.ts"/>
import * as util from 'util';
import * as State from "./State";
import * as TypeImpls from "../typing/TypeImpls";
import * as TypeInferencer from "../typing/TypeInferencer";
import * as AST from "../TraceLanguageAST";
import * as Misc from "../Misc";
import * as VariableManager from "../VariableManager";
import * as CalleeMatcher from "../typing/CalleeMatcher";
import * as TypeLattices from "../typing/TypeLattices";

interface SimpleTypes {
    Number: TupleType
    String: TupleType
    Boolean: TupleType
    Undefined: TupleType
    Null: TupleType
    None: TupleType
    Top: TupleType
    TopFunction: FunctionType
    NoneFunction: FunctionType
}

interface CallMonitor {
    enter(iid:string, scopeID:ScopeID, fun:FunctionType, base:TupleType, args:TupleType[]):void
    call(iid:string):void
    return():void
}

interface CallAbstractor {
    abstract(scopeID:ScopeID): ScopeID
    getMonitor(): CallMonitor
}

interface RecoverPropertyTypeFunc {
    ():TupleType
}

interface RecoveryMarkedExpressionResult {
    recovered?: boolean
    result: TupleType
}
/**
 * Returns the type or *undefined* of an expression. An undefined return value indicates that some initial type environment should be used for the value instead.
 */
class ExpressionDataflowVisitor implements TraceExpressionVisitor<RecoveryMarkedExpressionResult> {
    constructor(private variables:RecoveryMarkedVariables<TupleType>, private inferredEnv:Variables<TupleType>) {
    }

    visitRead(e:Read):RecoveryMarkedExpressionResult {
        return {recovered: this.variables.isRecovered(e.source), result: this.variables.read(e.source)};
    }

    visitFieldRead(e:FieldRead):RecoveryMarkedExpressionResult {
        var base:ObjectType;
        var potentialObjectBaseTuple = this.variables.read(e.base);
        if (TypeImpls.TupleAccess.isObject(potentialObjectBaseTuple)) {
            base = TypeImpls.TupleAccess.getObject(potentialObjectBaseTuple);
        } else {
            // precision lost: an object must be present at this location, so read it from the inferred environment
            base = TypeImpls.TupleAccess.getObject(this.inferredEnv.read(e.base));
        }

        var property:TupleType;
        var nonsensicalReadFallback:RecoveryMarkedExpressionResult = null;
        switch (base.objectKind) {
            case TypeImpls.ObjectKinds.Some:
                var baseObject = <ObjectType> base;
                var n = Misc.fieldNameAbstraction(e.fieldName, base.objectClassification);
                if (Misc.HOP(baseObject.properties, n)) {
                    property = baseObject.properties[n];
                    if (property !== undefined && TypeImpls.constants.Top !== property && TypeImpls.TupleAccess.isRecursiveReference(property)) {
                        throw new Error("." + n + " has a recursive reference: " + TypeImpls.toPrettyString(property));
                    }
                    return {result: property};
                } else {
                    return nonsensicalReadFallback;
                }
            case TypeImpls.ObjectKinds.Top:
            case TypeImpls.ObjectKinds.Bottom:
                return nonsensicalReadFallback;
            default:
                throw new Error("Unhandled case: " + base.objectKind);
        }
    }

    visitNew(e:New):RecoveryMarkedExpressionResult {
        return undefined;
    }

    visitPrimitiveExpression(e:PrimitiveExpression):RecoveryMarkedExpressionResult {
        return undefined;
    }
}

class StatementDataflowVisitor implements TraceStatementVisitor<void> {
    private flowStoppingVariables = new Set<Variable>(); // variables whose value are controlled elsewhere
    private matchedCalleeReturnTypeStack:TupleType[] = [];

    constructor(private expressionVisitor:TraceExpressionVisitor<RecoveryMarkedExpressionResult>,
                private variables:RecoveryMarkedVariables<TupleType>,
                private inferredEnv:Variables<TupleType>,
                private callMonitor:CallMonitor,
                private lattice:CompleteLattice<TupleType>,
                private isAssignmentCompatible:(to:TupleType, from:TupleType) => boolean) {

    }

    visitWrite(e:Write):void {
        // TODO refactor to avoid null/undefined/{recovered,result}...
        var rhs = e.rhs.applyExpressionVisitor(this.expressionVisitor);

        var result:TupleType;
        if (this.flowStoppingVariables.has(e.sink)) {
            // console.log("Skipping flow %s into %s, reusing: %s", TypeImpls.toPrettyString(rhs.result), VariableManager.variableToString(e.sink), TypeImpls.toPrettyString(result));
            return;
        } else if (rhs === undefined) {// value-expressions return 'undefined', materialize the type from the inferred environment
            result = this.inferredEnv.read(e.sink);
        } else if (rhs === null/* special signaling value that the read did not produce a type */) {
            result = this.inferredEnv.read(e.sink);
            this.variables.markRootRecovered(e.sink);
        } else {
            if (rhs.recovered) {
                this.variables.markTransitivelyRecovered(e.sink);
            }
            result = rhs.result;
        }

        this.variables.write(e.sink, result);
    }

    visitFieldWrite(e:FieldWrite):void {
        // ignore!
    }

    visitDelete(e:Delete):void {
        // ignore!
    }

    visitInfo(e:Info):void {
        // NB: always generates reads for call-related variables to avoid treating them as dead (calls should be first order in the trace language)
        switch (e.kind) {
            case AST.InfoKinds.FunctionResult:
            function hasTypeParameters(type:TupleType) {
                if(type === undefined){
                    return false;
                }
                if(TypeImpls.isTupleTypeEqual(type, TypeImpls.constants.Top)){
                    return false;
                }
                return  (TypeImpls.TupleAccess.isTypeParameter(type) ||
                    (TypeImpls.TupleAccess.isObject(type) && (Object.keys(TypeImpls.TupleAccess.getObject(type).properties)).some(p => TypeImpls.TupleAccess.isTypeParameter(TypeImpls.TupleAccess.getObject(type).properties[p]))));
            }

                var returnType = this.matchedCalleeReturnTypeStack.pop();
                this.flowStoppingVariables.add(e.properties.resultTmp);
                if (hasTypeParameters(returnType)) { // TODO instantiate properly, this is overly precise
                    this.variables.write(e.properties.resultTmp, this.inferredEnv.read(e.properties.resultTmp));
                }else{
                    this.variables.write(e.properties.resultTmp, returnType);
                }
                break;
            case AST.InfoKinds.FunctionEnter:
                this.flowStoppingVariables.add(e.properties.functionTmp);
                this.variables.write(e.properties.functionTmp, this.inferredEnv.read(e.properties.functionTmp));
                this.flowStoppingVariables.add(e.properties.baseTmp);
                this.variables.write(e.properties.baseTmp, this.inferredEnv.read(e.properties.baseTmp));
                e.properties.argsTmps.forEach(argTmp => {
                    this.flowStoppingVariables.add(argTmp);
                    this.variables.write(argTmp, this.inferredEnv.read(argTmp));
                });
                if (this.callMonitor) {
                    var args = e.properties.argsTmps.map(tmp => this.inferredEnv.read(tmp));
                    var base = this.inferredEnv.read(e.properties.baseTmp);
                    var fun = TypeImpls.TupleAccess.getFunction(this.inferredEnv.read(e.properties.functionTmp));
                    this.callMonitor.enter(e.meta.iid, e.properties.scopeID, fun, base, args);
                }
                break;
            case AST.InfoKinds.FunctionInvocation:
                var callInputs = CalleeMatcher.getInputs(e.properties.functionTmp, e.properties.baseTmp, e.properties.argsTmps, this.lattice, this.variables, this.inferredEnv);
                var matchResult = CalleeMatcher.match(callInputs.callee, callInputs.base, callInputs.args, this.isAssignmentCompatible, e.properties.isConstructorCall);
                var returnTypes = matchResult.matches.map(match => match.result);
                if (matchResult.isTop) {
                    returnTypes.push(TypeImpls.constants.Top);
                }
                var returnType = returnTypes.reduce<TupleType>(this.lattice.lub, returnTypes[0]);
                this.matchedCalleeReturnTypeStack.push(returnType);

                if (this.callMonitor) {
                    this.callMonitor.call(e.meta.iid);
                }
                break;
            case AST.InfoKinds.FunctionReturn:
                this.variables.read(e.properties.resultTmp);
                if (this.callMonitor) {
                    this.callMonitor.return();
                }
                break;
            case AST.InfoKinds.Coerce:
            case AST.InfoKinds.ForInObject:
            case AST.InfoKinds.NextNewIsArray:
            case AST.InfoKinds.NextNewIsArguments:
            case AST.InfoKinds.NextNewIsFunction:
            case AST.InfoKinds.NextFieldAccessIsDynamic:
            case AST.InfoKinds.NextNewIsDotPrototype:
                // ignore
                break;
            default:
                throw new Error("Unhandled info kind: " + e.kind);
        }
    }
}

// FIXME: identify the rare non-monotonicity bug
var nonMonotonicityHack:Map<Variable, number>;
/**
 * Implementation of flow & context insensitivity. + monitoring
 *
 * - Flow insensitivity means that named local variables are updated weakly (should not be surprising)
 * - Context insensitivity means that unnamed variables are weakly updated across calls (a bit counter intuitive, see below).
 *
 * As the rhs of every named lhs/rhs of named local variables reads/writes always are unnamed variables, the context insensitivity is effectively achieved for the values of the named local variables!
 * If context insensitivity was implemented by sharing named local variables across contexts, then recursive calls would misbehave.
 * (see examples in /test/TypedTraceReplayerTests)
 */
class MonitoredAbstractedVariables implements RecoveryMarkedVariables<TupleType> {
    public dirty = false;

    private variables = new State.VariablesImpl<TupleType>();

    private reads = new Set<Variable>();
    private writes = new Set<Variable>();

    private abstractionCache = new Map<Variable, Variable>(); // concrete variable -> abstracted variable
    private reverseAbstraction = new Map<Variable, Set<Variable>>(); // abstracted variable -> concrete variables

    // the unabstracted variables that has been directly assigned a recovered type
    private rootRecovered = new Set<Variable>();
    // the unabstracted variables that has been read since being assigned a transitively recovered type
    private usedRecovered = new Set<Variable>();
    // the abstracted variables that transitively has been assigned a recovered type
    private transitivelyRecovered = new Set<Variable>();

    // the unabstracted variables and their iid write location
    private writeLocationMap = new Map<Variable, string>();
    // the unabstracted variables and their iid read locations
    private readLocationMap = new Map<Variable, Set<string>>();

    private readLocationMapWithTopDueToRecursion = new Map<Variable, Set<string>>();

    constructor(private lattice:CompleteLattice<TupleType>, private flowConfig:PrecisionConfig, private callAbstractor:CallAbstractor, private currentIIDBox:{iid: string}) {
    }

    private abstract(variable:Variable):Variable {
        if (this.abstractionCache.has(variable)) {
            return this.abstractionCache.get(variable);
        }
        var abstractVariable:Variable = {named: variable.named};

        var killCallContext = this.flowConfig.contextInsensitiveVariables && !variable.named;

        if (variable.iid) {
            abstractVariable.iid = variable.iid;
        }
        if (variable.name) {
            abstractVariable.name = variable.name;
        }
        if (variable.functionIID) {
            abstractVariable.functionIID = variable.functionIID;
        }
        if (variable.callCount && !killCallContext) {
            var scopeID = variable.functionIID + ":" + variable.callCount /* TODO avoid this manual mapping that requires knowledge of encodings.. */;
            var abstractScopeID = this.callAbstractor.abstract(scopeID);
            if (abstractScopeID !== undefined) {
                abstractVariable.callCount = abstractScopeID;
            } else {
                abstractVariable.callCount = variable.callCount;
            }
        }
        var canonicalized = VariableManager.canonicalize(abstractVariable);
        this.abstractionCache.set(variable, canonicalized);
        if (!this.reverseAbstraction.has(canonicalized)) {
            this.reverseAbstraction.set(canonicalized, new Set<Variable>());
        }
        this.reverseAbstraction.get(canonicalized).add(variable);
        return canonicalized;
    }

    read(variable:Variable) {
        if (!this.readLocationMap.has(variable)) {
            this.readLocationMap.set(variable, new Set<string>());
        }
        this.readLocationMap.get(variable).add(this.currentIIDBox.iid);
        this.reads.add(variable);
        if (this.isRecovered(variable)) {
            this.usedRecovered.add(variable);
        }
        var result = this.variables.read(this.abstract(variable));

        var isObjectTop = TypeImpls.TupleAccess.isObject(result) && TypeImpls.TupleAccess.getObject(result) === TypeImpls.constants.ObjectTop;
        var isObjectTopDueToRecursion = TypeImpls.TupleAccess.isObjectTopDueToRecursion(result);
        if (isObjectTopDueToRecursion) {
            console.log("BANG!");
            if (!this.readLocationMapWithTopDueToRecursion.has(variable)) {
                this.readLocationMapWithTopDueToRecursion.set(variable, new Set<string>());
            }
            this.readLocationMapWithTopDueToRecursion.get(variable).add(this.currentIIDBox.iid);
        } else if (isObjectTop) {
            //console.log("BOOM!");
        }
        return result;
    }

    write(variable:Variable, typeToWrite:TupleType) {
        this.writeLocationMap.set(variable, this.currentIIDBox.iid);
        this.writes.add(variable);
        var resultType = typeToWrite;
        if (resultType === undefined /* TODO rethink/document the need for this guard */) {
            return;
        }
        var abstractVariable = this.abstract(variable);
        var oldType = this.variables.read(abstractVariable, true);
        var doWeakUpdateToNamedVariable = this.flowConfig.flowInsensitiveVariables && variable.named;
        var doWeakUpdateToUnnamedVariable = (this.flowConfig.contextInsensitiveVariables || this.flowConfig.callstackSensitiveVariables) && !variable.named;
        var doWeakUpdate = doWeakUpdateToNamedVariable || doWeakUpdateToUnnamedVariable || variable.forceMerge;
        if (oldType !== undefined && doWeakUpdate) {
            resultType = this.lattice.lub(resultType, oldType);
        }

        if (oldType === undefined || !TypeImpls.isTupleTypeEqual(resultType, oldType)) {
            if (!this.dirty && doWeakUpdate) {
                if (!nonMonotonicityHack.has(abstractVariable)) {
                    nonMonotonicityHack.set(abstractVariable, 0);
                }
                nonMonotonicityHack.set(abstractVariable, nonMonotonicityHack.get(abstractVariable) + 1);
                if (nonMonotonicityHack.get(abstractVariable) > 50) {
                    resultType = this.lattice.lub(resultType, new TypeImpls.TupleTypeImpl([TypeImpls.constants.ObjectTop]));
                }
                var BUGHUNT = false;
                if (BUGHUNT) {
                    console.log("First type change at: %s: \n\t%s \n\t\t-> \n\t%s", JSON.stringify(abstractVariable), oldType === undefined ? "-" : TypeImpls.toPrettyString(oldType), TypeImpls.toPrettyString(resultType));
                    console.log("# changes here: %d", nonMonotonicityHack.get(abstractVariable));
                    if (oldType !== undefined) {
                        TypeImpls.isTupleTypeEqual(resultType, oldType, true)
                    }
                }
                this.dirty = true;
            }
            this.variables.write(abstractVariable, resultType);
        }
    }

    markRootRecovered(variable:Variable) {
        this.rootRecovered.add(variable);
        this.markTransitivelyRecovered(variable);
    }

    markTransitivelyRecovered(variable:Variable) {
        this.transitivelyRecovered.add(this.abstract(variable));
    }

    isRecovered(variable:Variable) {
        return this.transitivelyRecovered.has(this.abstract(variable));
    }

    getRecoveryData():RecoveryData {
        var reverseAbstraction = this.reverseAbstraction;

        function unabstract(abstracted:Set<Variable>) {
            var concrete = new Set<Variable>();
            abstracted.forEach(a => {
                reverseAbstraction.get(a).forEach(c => concrete.add(c));
            });
            return concrete;
        }

        return {roots: this.rootRecovered, uses: this.usedRecovered};
    }

    getDeadVariables():Set<Variable> {
        var dead = new Set<Variable>();
        this.writes.forEach(v => {
            if (!this.reads.has(v)) {
                dead.add(v)
            }
        });
        return dead;
    }

    getLiveVariables():Set<Variable> {
        var live = new Set<Variable>();
        this.reads.forEach(v => live.add(v));
        return live;
    }

    getReadLocationMap() {
        return this.readLocationMap;
    }

    getWriteLocationMap() {
        return this.writeLocationMap;
    }

    countLocationsWithTopDueToRecursion() {
        return this.readLocationMapWithTopDueToRecursion.size;
    }
}

class NoCallAbstraction implements CallAbstractor {
    public abstract(scopeID:ScopeID):ScopeID {
        return scopeID;
    }

    public getMonitor():CallMonitor {
        return undefined;
    }
}

class SyntacticCallstackAbstraction implements CallAbstractor {
    private monitor:CallMonitor;
    private scopeIDAbstraction = new Map<ScopeID, string>();
    private stackIDMap = new Map<string, number>();

    constructor(k:number) {
        var stack:string[] = [];
        var scopeIDAbstraction = this.scopeIDAbstraction;
        var stackIDMap = this.stackIDMap;
        this.monitor = {
            call(iid:string) {
                //console.log('call(%s)', iid);
                stack.push(iid);
            },
            enter(iid:string, scopeID:ScopeID, fun:FunctionType, base:TupleType, args:TupleType[]) {
                //console.log('enter(%s)', scopeID);
                if (k != -1 && stack.length > k) {
                    stack = stack.slice(stack.length - k)
                }
                var stackString = stack.join("->");
                if (!stackIDMap.has(stackString)) {
                    stackIDMap.set(stackString, stackIDMap.size);
                }
                scopeIDAbstraction.set(scopeID, '' + stackIDMap.get(stackString))
            },
            return(){
                //console.log('return');
                stack.pop();
            }
        };
    }

    public abstract(scopeID:ScopeID):ScopeID {
        return this.scopeIDAbstraction.get(scopeID);
    }

    public getMonitor():CallMonitor {
        return this.monitor;
    }

}
interface FunctionEntry {
    iid: string
    parameters: TupleType[]
}
class GenericParameterInstantiationsCallStackAbstraction implements CallAbstractor {
    private monitor:CallMonitor;
    private scopeIDAbstraction = new Map<ScopeID, string>();

    constructor() {
        var scopeIDAbstraction = this.scopeIDAbstraction;

        function getInstantiation(iid:string, fun:SingleFunctionType, base:TupleType, args:TupleType[]):TupleType {
            var pairs:[TupleType, TupleType][] = []

            pairs.push([fun.base, base]);
            for (var i = 0; i < args.length; i++) {
                pairs.push([fun.args[i], args[i]]);
            }

            pairs = pairs.concat(Array.prototype.concat.apply([], pairs.
                filter(pair => TypeImpls.TupleAccess.isObject(pair[0]) && TypeImpls.TupleAccess.isObject(pair[1])).
                map(pair => [TypeImpls.TupleAccess.getObject(pair[0]), TypeImpls.TupleAccess.getObject(pair[1])]).
                map((objectPair:[ObjectType,ObjectType]):[TupleType, TupleType][]=> {
                    var declared = objectPair[0];
                    var actual = objectPair[1];
                    var names = Object.keys(declared.properties);
                    var result:[TupleType, TupleType][] = names.map((n:string):[TupleType, TupleType] => {
                        var declaredPropertyType = declared.properties[n];
                        var actualPropertyType = actual.properties[n] || TypeImpls.constants.Bottom /* does this even occur? */;
                        return [declaredPropertyType, actualPropertyType];
                    });
                    return result;
                })
            ));

            for (var p in pairs) {
                var pair = pairs[p];
                if (TypeImpls.TupleAccess.isTypeParameter(pair[0]) && !TypeImpls.isTupleTypeEqual(TypeImpls.constants.Top, pair[0])) {
                    // no need to check if other type parameters have the same type -- they always do!
                    // (because the function type is inferred by actual argument values, and those are the ones we read here!)
                    return pair[1];
                }
            }
            return null;
        }

        this.monitor = {
            call(iid:string) {
            },
            enter(iid:string, scopeID:ScopeID, fun:FunctionType, base:TupleType, args:TupleType[]) {
                var abstractScopeID:string;
                if (fun.functionKind === TypeImpls.FunctionKinds.Single) {
                    var instantiation = getInstantiation(iid, <SingleFunctionType>fun, base, args);
                    if (instantiation) {
                        abstractScopeID = util.format("%s w. E as %s", iid, TypeImpls.toPrettyString(instantiation) /* TODO make this safer: it is bad to rely on the toString method!! */);
                    }
                }
                abstractScopeID = abstractScopeID || iid;
                // console.log("%s as %s for %s", scopeID, abstractScopeID, TypeImpls.functionToPrettyString(fun));
                scopeIDAbstraction.set(scopeID, abstractScopeID);

            },
            return(){
                //console.log('return');
            }
        };
    }

    public abstract(scopeID:ScopeID):ScopeID {
        return this.scopeIDAbstraction.get(scopeID);
    }

    public getMonitor():CallMonitor {
        return this.monitor;
    }
}
class ParameterTypesCallstackAbstraction implements CallAbstractor {
    private monitor:CallMonitor;
    private scopeIDAbstraction = new Map<ScopeID, string>();
    private stackIDMap = new Map<string/*iid. Not strictly required, but it gives a large speedup */, Map<FunctionEntry[], string /* id */>>();

    constructor(k:number) {
        var stack:FunctionEntry[] = [];
        var scopeIDAbstraction = this.scopeIDAbstraction;
        var stackIDMap = this.stackIDMap;
        var nextParameters:TupleType[];

        function getRepresentative(entryStack:FunctionEntry[], candidateStacksMap:Map<FunctionEntry[], string>):FunctionEntry[] {
            var candidateStacks:FunctionEntry[][] = [];
            candidateStacksMap.forEach((v, k) => candidateStacks.push(k));
            var entryStackTop = entryStack[entryStack.length - 1];
            var iid = entryStackTop.iid;
            var stackMatches = candidateStacks.filter(candidateStack => {
                if (candidateStack.length !== entryStack.length) {
                    return false;
                }
                for (var stackIndex = 0; stackIndex < candidateStack.length; stackIndex++) {
                    var entryStackElement = entryStack[stackIndex];
                    var candidateStackElement = candidateStack[stackIndex];
                    var equalIID = iid === candidateStackElement.iid;
                    if (!equalIID) {
                        return false;
                    }

                    if (entryStackElement.parameters.length !== candidateStackElement.parameters.length) {
                        return false;
                    }
                    for (var i = 0; i < entryStackElement.parameters.length; i++) {
                        var entryParameter = entryStackElement.parameters[i];
                        var candidateParameter = candidateStackElement.parameters[i];
                        if (!TypeImpls.isTupleTypeEqual(entryParameter, candidateParameter)) {
                            return false;
                        }
                    }
                }
                return true;
            });

            var representative:FunctionEntry[];
            if (stackMatches.length === 0) {
                stackIDMap.get(entryStackTop.iid).set(entryStack, iid + stackIDMap.get(iid).size + '');
                representative = entryStack;
            } else if (stackMatches.length === 1) {
                representative = stackMatches[0];
            } else {
                throw new Error("Multiple FunctionEntry matches: " + stackMatches);
            }
            return representative;
        }

        this.monitor = {
            call(iid:string) {
            },
            enter(iid:string, scopeID:ScopeID, fun:FunctionType, base:TupleType, args:TupleType[]) {
                var entry = {iid: iid, parameters: args};
                stack.push(entry);
                //console.log('enter(%s)', scopeID);
                if (k !== -1 && stack.length > k) {
                    stack = stack.slice(stack.length - k)
                }

                if (!stackIDMap.has(iid)) {
                    stackIDMap.set(iid, new Map<FunctionEntry[], string>());
                }
                var representative = getRepresentative(stack.slice(), stackIDMap.get(iid));
                scopeIDAbstraction.set(scopeID, '' + stackIDMap.get(iid).get(representative))
            },
            return(){
                //console.log('return');
                stack.pop();
            }
        };
    }

    public abstract(scopeID:ScopeID):ScopeID {
        return this.scopeIDAbstraction.get(scopeID);
    }

    public getMonitor():CallMonitor {
        return this.monitor;
    }

}

function replayStatements(inferredEnv:Variables<TupleType>, varibleList:Variable[], statements:TraceStatement[], flowConfig:PrecisionConfig, lattice:CompleteLattice<TupleType>, explainer:MetaInformationExplainer):{
    propagatedEnv: Variables<TupleType>
    inferredEnv: Variables<TupleType>
} {
    var callstackAbstraction:CallAbstractor;

    var callAbstraction:CallAbstractor;
    var callstackSensitiveVariables = flowConfig.callstackSensitiveVariables;
    if (callstackSensitiveVariables) {
        var k = callstackSensitiveVariables.height === undefined ? -1 : callstackSensitiveVariables.height;
        switch (callstackSensitiveVariables.sensitivity) {
            case CallStackSensitivity.CallSite:
                callAbstraction = new SyntacticCallstackAbstraction(k);
                break;
            case CallStackSensitivity.ParameterValues:
                callAbstraction = new ParameterTypesCallstackAbstraction(k);
                break;
            case CallStackSensitivity.GenericParameterInstantiations:
                callAbstraction = new GenericParameterInstantiationsCallStackAbstraction();
                break;
            default:
                throw new Error("Unhandled case: " + callstackSensitiveVariables.sensitivity);
        }
    } else {
        callAbstraction = new NoCallAbstraction();
    }

    var iidBox = {iid: statements[0].meta.iid};
    var variablesDecorator = new MonitoredAbstractedVariables(lattice, flowConfig, callAbstraction, iidBox);
    var iterationCount = 0;
    var start = new Date();
    do {
        iterationCount++;
        if (iterationCount > 10000) {
            throw new Error("Not likely to terminate - probably a non-monotoniticy issue, set BUGHUNT = true in TypedTraceReplayer.ts...");
        }
        var roundStart = new Date();
        // console.log("Type propagation round #%d", iterationCount);
        variablesDecorator.dirty = false;
        var replayState = {
            currentTraceIndex: 0,
            variables: variablesDecorator,
            trace: statements
        };

        var expressionVisitor = new ExpressionDataflowVisitor(replayState.variables, inferredEnv);

        var statementDataflowVisitor = new StatementDataflowVisitor(expressionVisitor, replayState.variables, inferredEnv, callAbstraction.getMonitor(), lattice, TypeLattices.makeAssignmentCompatibilityCheck(lattice));

        statements.forEach(function (statement) {
            iidBox.iid = statement.meta.iid;
            // console.log(statement.toString());
            statement.applyStatementVisitor(statementDataflowVisitor);
            replayState.currentTraceIndex++;
        });
        var roundEnd = new Date();
        // console.log("Variable type fix point iteration #%d took %d ms", iterationCount, roundEnd.getTime() - roundStart.getTime());
    } while ((flowConfig.flowInsensitiveVariables || flowConfig.contextInsensitiveVariables || callstackSensitiveVariables) && variablesDecorator.dirty);

    if (false) {
        showRecoveryInformation(replayState.variables, explainer);
    }
    if (false) {
        console.log("TopDueToRecursion-count: %d", variablesDecorator.countLocationsWithTopDueToRecursion());
    }

    var end = new Date();
    // console.log("Variable type fix point found after %d iterations and %d ms", iterationCount, end.getTime() - start.getTime());
    return {propagatedEnv: variablesDecorator, inferredEnv: inferredEnv};
}

function showRecoveryInformation(variables:MonitoredAbstractedVariables, explainer:MetaInformationExplainer) {
    function intersect<T>(s1:Set<T>, s2:Set<T>):Set<T> {
        var intersected = new Set<T>();
        s1.forEach(e => {
            if (s2.has(e)) {
                intersected.add(e);
            }
        });
        return intersected;
    }

    function getReadLocationStrings(s:Set<Variable>):Set<string> {
        var locations = new Set<string>();
        s.forEach(v => {
            var readIIDs = variables.getReadLocationMap().get(v);
            readIIDs.forEach(iid => locations.add(explainer.getIIDSourceLocation(iid).toString()));
        });
        return locations;
    }

    function getWriteLocationStrings(s:Set<Variable>):Set<string> {
        var locations = new Set<string>();
        s.forEach(v => {
            locations.add(explainer.getIIDSourceLocation(variables.getWriteLocationMap().get(v)).toString());
        });
        return locations;
    }

    var recoveryData = variables.getRecoveryData();
    var live = variables.getLiveVariables();
    var liveRoots = intersect(recoveryData.roots, live);
    var rootVarCount = liveRoots.size;
    var useVarCount = recoveryData.uses.size;
    var varRatio = (rootVarCount === 0) ? 0 : useVarCount / rootVarCount;
    var rootLocCount = getWriteLocationStrings(liveRoots).size;
    var useLocCount = getReadLocationStrings(recoveryData.uses).size;
    var locRatio = (rootLocCount === 0) ? 0 : useLocCount / rootLocCount;
    console.log("by vars: %d / %d = %d", useVarCount, rootVarCount, varRatio);
    console.log("by locs: %d / %d = %d", useLocCount, rootLocCount, locRatio);
    console.log('"%d","%d","%d","%d";', useVarCount, rootVarCount, useLocCount, rootLocCount);
}
export function replayTrace(variableValues:Map<Variable, Value[]>, variableList:Variable[], statements:TraceStatement[], flowConfig:PrecisionConfig, valueTypeConfig:ValueTypeConfig, explainer:MetaInformationExplainer):{
    propagatedEnv: Variables<TupleType>
    inferredEnv: Variables<TupleType>
} {
    nonMonotonicityHack = new Map<Variable, number>();
    // console.log("Flow-less type inference...");
    var inferencer:TypeInferencer = new TypeInferencer.TypeInferencerImpl(valueTypeConfig.types, valueTypeConfig.initialFunctionTypeMaker, !!valueTypeConfig.useSJSAscription);
    var inferredEnv = new State.VariablesImpl<TupleType>();
    console.log("Type ascription...");
    variableList.filter(v => !v.named).forEach(variable => {
            var type = variableValues.get(variable).reduce((t:TupleType, v:Value) =>
                valueTypeConfig.types.lub(t, inferencer.getAscriber().ascribeType(v, [util.format("VAR(%s)", VariableManager.variableToString(variable))])), valueTypeConfig.types.bot);

            if (TypeImpls.TupleAccess.isRecursiveReference(type) && type !== TypeImpls.constants.Top) {
                throw new Error("Recursive references should have been resolved by now: " + TypeImpls.toPrettyString(type));
            }
            inferredEnv.write(variable, type)
        }
    );

    console.log("Type propagation...");
    return replayStatements(inferredEnv, variableList, statements, flowConfig, valueTypeConfig.types, explainer);
}


export enum CallStackSensitivity{
    ParameterValues,
    CallSite,
    GenericParameterInstantiations
}