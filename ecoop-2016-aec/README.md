# Trace Typing Artifact

This page documents how to reproduce the results described in the
ECOOP 2016 paper "Trace Typing: An Approach for Evaluating Retrofitted
Type Systems." The artifact is specifically designed to help reproduce
the results described in the Experiments sections of the paper. It can
also be used to test out Trace Typing on other applications.

Note that the artifact is meant to be consistent with the paper, but
minor bug fixes has been done since submission, so the exact numbers
might vary a little.

## Installation

Our virtual machine is (also) available
[here](https://filesender.deic.dk/filesender/?vid=236443cb-f6c8-3d28-23ac-00002f66582b)
(1.7GB, md5 77a980c89ad9fed5941a46522f013896). Here is some
information about the machine:

- username / password: tracetyping / tracetyping
- RAM: 2048MB

The tracetyping home directory contains the directory structure:

```
- trace-typing
-- trace-production // the Trace Collector implementation
-- trace-typing // the Trace Typer implementation
-- ecoop-2016-aec
--- README.md // this file
--- reproduce // script for reproducing results
--- expected-outputs // expected outputs for runs of the reproduce script
```

Since the VM itself requires 2GB RAM, we recommend running it on a
machine with at least 8GB RAM, though it may run elsewhere.

## Reproducing results

This section explains how to reproduce the results of the paper.  They
all rely on execution of the
[/ecoop-2016-aec/reproduce](/ecoop-2016-aec/reproduce) script. The script is
just a wrapper for more complex invocations of the Trace Typing
system, the curious reviewer should look in the script to see how
customized experiments can be made.

Since it takes a long time to reproduce *all* the results of the
paper, the script only reproduces *some* of the results. Minor
adjustments of the script are needed to reproduce all the results.

For simplicity, the trace for each analysed application is not reused;
it is re-created in each run. This increases running time a little.

### Getting started

1. Start the virtual machine
2. You will be logged in as the tracetyping user automatically
3. Open up a terminal (shortcut available on the desktop)
4. Type `cd ~/trace-typing`

### 6.2 Comparing Type System Variants

Run the command:
```
$ ecoop-2016-aec/reproduce variants-0
```

Example output:

```
Type ascription...
Type propagation...
Failure information (51 entries):
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:616:3: Invalid assignment to .prototype of type {all, any, async, chunk, collect, compact, concat, consecutive, contains, countBy, 

...

    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy.node_orig_.js:177:21: .extensions does not exist on object <I(x2)>
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy.node_orig_.js:179:1: .extensions does not exist on object <I(x2)>
/Failure information (51 entries)

Finished 'Comparing Type System Variants' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/lazy.js/main.js using system  union|intersect
```

Each line of the output shows the location of a type error when some
trace type system is applied to some application.  The last line shows
the total number of errors, this number is the number used in Appendix
B.

The output for another trace type system and application combination
can be seen by running the command:

```
$ ecoop-2016-aec/reproduce variants-1
```
Example output:

```
Type ascription...
Type propagation...
Type checked 100000 statements
Failure information (243 entries):
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:6:2: Should not be the Top function
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:15:28: ._ does not exist on object {}
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:41:38: Should not be the Top function

...

/Failure information (243 entries)

Finished 'Comparing Type System Variants' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/underscore/main.js using system  subtyping|base
```

### 6.3 Finding Tag Tests

Run the command:
```
$ ecoop-2016-aec/reproduce tags-0
```

Example output:
```
Replaying...
Type ascription...
Type propagation...
Finding successiveReads ...
|successiveReads|: 8811
Finding refinedReads ...
|refinedReads|: 11
Outputting ...
out/type-guard-lines/lazy_orig_.js@760c9573751f82725d8c6cc6bd0b5f91.txt
../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:94     if (source instanceof Array) {
../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:5790     switch (typeof callback) {
../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:1030     if (handle instanceof AsyncHandle) {

Finished 'Finding Tag Tests' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/lazy.js/main.js
```

Each line contains the source code and line number for a type guard.

To reproduce the results of the paper, a manual classification session
is now required. The result of the classification for all applications
can be seen
[here](https://docs.google.com/spreadsheets/d/1AfYKWar8d_adW6z-tzxqbXSnTF7UTtxKtZbBtcaHaJI/edit?usp=sharing). Notice
that the document contains more data than what is described in the
paper, the numbers in Table 1 in the paper are derived from row 2
and 3.

- Example 1: the number of identified type guards are 164 since the column sum for row 2 and 3 is 164.
- Example 2: the number of typeof type guards are 30 since cell D3 is 30.

The output for the tags in another application can be seen by running
the command:

```
$ ecoop-2016-aec/reproduce tags-1
```
Example output:

```
Replaying...
Type ascription...
Type propagation...
Finding successiveReads ...
|successiveReads|: 460957
Finding refinedReads ...
|refinedReads|: 498
Outputting ...
out/type-guard-lines/underscore_orig_.js@f7f4e7c0fef404879d572945ce71580f.txt
../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:151     if (isArrayLike(obj)) {
../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:1371     return _.isFunction(value) ? value.call(object) : value;

...

../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:1197     if (isArrayLike(obj) && (_.isArray(obj) || _.isString(obj) || _.isArguments(obj))) return obj.length === 0;
../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:1368     if (value === void 0) {
../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:1027     if (_.isFunction(oiteratee)) {

Finished 'Finding Tag Tests' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/underscore/main.js
```

### 6.4 Evaluating Fixed Object Layout

Run the command:
```
$ ecoop-2016-aec/reproduce fixed-0
```

Example output:
```
Type ascription...
Type propagation...
Failure information (116 entries):
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:618:3: .getIterator is read-only
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:622:3: .each is read-only
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:745:3: .getIterator is read-on

...

    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy_orig_.js:5551:3: .each is read-only
    ../out/instrumentations/lazy.js/node_modules/lazy.js/lazy.node_orig_.js:33:1: .each is read-only
/Failure information (116 entries)

Finished 'Evaluating Fixed Object Layout' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/lazy.js/main.js
```

Similiar to the 6.2 results, this shows the number of type errors for
the fixed object layout trace typing system applied to some
application. This run found 116 fixed object layout specific type
errors, corresponding to the "114" and "2" in the the "lazy.js" row of
Table 2.


The output for another application can be seen by running the command:

```
$ ecoop-2016-aec/reproduce fixed-1
```

Example output:
```
Type ascription...
Type propagation...
Type checked 100000 statements
Failure information (3 entries):
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:39:11: Instance property types are not invariant wrt. the prototype properties
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:711:3: .bind is read-only
    ../out/instrumentations/underscore/node_modules/underscore/underscore_orig_.js:1493:18: .bind is read-only
/Failure information (3 entries)

Finished 'Evaluating Fixed Object Layout' for /home/esbena/_data/trace-typing/ecoop-2016-aec/../trace-production/tests/exercisedApps/underscore/main.js
```

The three type listed type errors correspond to the "1" and "2" in the
"underscore" row of Table 2.

## More experiments

The curious reviewer can try to modify
[/ecoop-2016-aec/reproduce](/ecoop-2016-aec/reproduce) to test the artifact
further. We have not tested all the configurations on the provided VM
image, memory might be an issue for some configurations.

### All benchmarks

The following directories contain the benchmarks of the paper:

- trace-production/tests/exercisedApps/escodegen
- trace-production/tests/exercisedApps/esprima
- trace-production/tests/exercisedApps/lazy.js
- trace-production/tests/exercisedApps/minimist
- trace-production/tests/exercisedApps/optparse
- trace-production/tests/exercisedApps/qs
- trace-production/tests/exercisedApps/typescript
- trace-production/tests/exercisedApps/underscore
- trace-production/tests/exercisedApps/xml2js

### All type systems

The following type system setups correspond to the ones in the tables in Figure 14:

- subtyping|base: ObjectFieldLubUnderSubtyping:FunctionPointwiseLub::flowInsensitiveVariables
- subtyping|poly: ObjectFieldLubUnderSubtyping:FunctionGenericTypeParameterOrLub::flowInsensitiveVariables
- subtyping|intersect: ObjectFieldLubUnderSubtyping:FunctionIntersection::flowInsensitiveVariables
- union|base: ObjectFieldLubUnderSubtyping:FunctionPointwiseLub::UnionTypes:flowInsensitiveVariables
- union|poly: ObjectFieldLubUnderSubtyping:FunctionGenericTypeParameterOrLub::UnionTypes:flowInsensitiveVariables
- union|intersect: ObjectFieldLubUnderSubtyping:FunctionIntersection::UnionTypes:flowInsensitiveVariables
