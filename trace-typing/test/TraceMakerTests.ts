///<reference path="../src/types.d.ts"/>

import * as assert from "./assert-async-mocha";
import * as path from "path";
import * as maker from "../src/TraceMaker";
import * as importer from "../src/TraceImporter";
var fixtures = path.resolve("fixtures");

describe("TraceMaker", function () {
    var aproximatePreambleSize = 3500;
    describe("getTraceFromSource", function () {
        it("should work on empty source", function (done) {
            maker.getTraceFromSource("", function (err: any, trace:Trace) {
                if(err){
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
        it("should work on non-empty source", function (done) {
            maker.getTraceFromSource("var a = 2 + 42;", function (err: any, trace:Trace) {
                if(err){
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
        it("should work on non-empty source 2", function (done) {
            maker.getTraceFromSource("var b = 2 + 42;", function (err: any, trace:Trace) {
                if(err){
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
    });
    describe("getTraceFromSourceFile", function () {
        it("should work on empty source", function (done) {
            maker.getTraceFromSourceFile(fixtures + "/empty.js", function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize,  done);
            });
        });
        it("should work on non-empty source", function (done) {
            var sourceFile = fixtures + "/non-empty.js";
            maker.getTraceFromSourceFile(sourceFile, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
    });
    describe("getTraceFromDir", function () {
        it("should work on multiple files", function (done) {
            var dir = fixtures + "/multiple-files-1";
            maker.getTraceFromDir({dir: dir, main: dir + "/main.js"}, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
        it("should work on node_modules of benchmark files", function (done) {
            var dir = fixtures + "/benchmark-copy-lazy.js-emptymain";
            this.timeout(10 * 1000);
            maker.getTraceFromDir({dir: dir, main: dir + "/main.js"}, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
        it("should work on requiring file from node_modules of benchmark files", function (done) {
            var dir = fixtures + "/benchmark-copy-lazy.js-requireonly";
            this.timeout(10 * 1000);
            maker.getTraceFromDir({dir: dir, main: dir + "/main.js"}, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize, done);
            });
        });
        it("should work on single benchmark files", function (done) {
            var dir = fixtures + "/benchmark-copy-lazy.js-singlefile";
            this.timeout(10 * 1000);
            maker.getTraceFromDir({dir: dir, main: dir + "/main.js"}, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize + 10000, done);
            });
        });
        it("should work on true benchmark file", function (done) {
            var dir = fixtures + "/benchmark-copy-lazy.js";
            this.timeout(10 * 1000);
            maker.getTraceFromDir({dir: dir, main: dir + "/main.js"}, function (err:any, trace:Trace) {
                if (err) {
                    done(err);
                    return;
                }
                assert.assert(trace.statements.length > aproximatePreambleSize + 10000, done);
            });
        });
    });
});