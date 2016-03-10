module.exports = function (grunt) {
    require("load-grunt-tasks")(grunt);
    var util = require('util');

    var ts_options = {
        target: 'es6',
        sourceMap: true,
        declaration: false,
        removeComments: true,
        noImplicitAny: true,
        compiler: './node_modules/typescript/bin/tsc'
    };
    var buildDir = 'build';
    var distDir = 'dist';
    grunt.initConfig({
        ts: {
            build: {
                src: ["src/**/*.ts"],
                outDir: buildDir,
                options: ts_options
            },
            test: {
                src: ["test/**/*.ts"], // will magically include 'src' folder as well, and therefore make build/src & build/test folders!
                outDir: buildDir,
                options: ts_options
            },
            play: {
                src: ["test/PlaygroundTests.ts"],
                outDir: buildDir,
                options: ts_options
            }
        },
        mochacli: {
            all: {options: {harmony: true, files: [distDir + '/test/*.js']}},
            play: {options: {harmony: true, files: [distDir + '/test/PlaygroundTests.js']}}
        },
        clean: [
            buildDir,
            distDir
        ],
        tsd: {
            refresh: {
                options: {
                    command: 'reinstall',
                    latest: true,
                    config: 'tsd.json'
                }
            }
        },
        shell: {
            options: {
                stderr: true
            },
            target: {
                command: util.format("node_modules/babel-cli/bin/babel.js %s --out-dir %s", buildDir, distDir)
            }
        }
    });

    grunt.loadNpmTasks('grunt-tsd');
    grunt.loadNpmTasks('grunt-ts');
    grunt.loadNpmTasks('grunt-contrib-clean');
    grunt.loadNpmTasks('grunt-mocha-cli');

    grunt.registerTask('shell-run', ['shell']);
    grunt.registerTask('default', ['test']);
    grunt.registerTask('test-only', ['mochacli']);
    grunt.registerTask('build', ['ts:build', 'ts:test', 'shell']);
    grunt.registerTask('test', ['clean', 'build', 'mochacli']);
    grunt.registerTask('play', ['ts:play', 'mochacli:play']);
    grunt.registerTask('deftyped', ['tsd']);
};



