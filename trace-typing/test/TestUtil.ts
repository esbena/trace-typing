import * as assert from "assert";
import * as path from "path";
import * as fs from "fs";
import * as util from 'util';
import * as TraceImporter from "../src/TraceImporter";

var oldBigApps = [/*'gulp', */ /*'lodash'*/, 'minimist', 'optparse', /*'express', 'grunt', */ 'lazy.js', 'underscore', /*'coffee-script'*/, 'escodegen'];

var newBigApps = ['esprima', 'qs', 'typescript', /*'validator',*/'xml2js', 'handlebars'];

var newNewBigApps:string[] = [];

var bigApps = oldBigApps.concat(newBigApps).concat(newNewBigApps);
//bigApps = bigApps.filter(app => app !== 'lodash');
bigApps = ['lazy.js'];
bigApps.sort();
var noBigApps = false;
var onlyBigApps = true;

export function getBenchmarkTraceFiles():string[] {


    var traceImporter:TraceImporter.TraceImporter = new TraceImporter.TraceImporter();

    return traceImporter.getAllTraceFiles().filter(f => !ignoreFile(f));
}

export function getBigApps() {
    return [].concat(bigApps)
}
export function ignoreFile(file:string) {
    var is_JSON_NaN_bug = file.indexOf("JSON_nan_bug") !== -1;
    var isBigApp = bigApps.some(app => file.indexOf(app) !== -1);
    return is_JSON_NaN_bug || (onlyBigApps && !isBigApp) || (noBigApps && isBigApp);
}