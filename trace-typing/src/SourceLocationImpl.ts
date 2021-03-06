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
///<reference path="./types.d.ts"/>
import * as path from "path";

export class SourceLocationImpl implements SourceLocation {
    public isPseudo:boolean = false;

    constructor(public file:string, public beginLine:number, public endLine:number, public beginColumn:number, public endColumn:number) {
    }

    toString(omitFile?:boolean, asRegion?:boolean, relative?:boolean) {

        if (this.isPseudo) {
            var result = this.file;
            if (relative) {
                result = path.relative(process.cwd(), result);
            }
            return result;
        }
        var result = "";
        if (!omitFile) {
            result += this.file;
            if (relative) {
                result = path.relative(process.cwd(), result);
            }
            result += ":";
        }
        result += this.beginLine + ":";
        result += this.beginColumn;

        if (asRegion) {
            result += "-"
            result += this.endLine + ":";
            result += this.endColumn;
        }
        return result;
    }
}

export function makeMissingIIDSourceLocation():SourceLocation {
    return {
        toString: function () {
            return "-missingIID-";
        },
        file: "",
        beginLine: -1,
        beginColumn: -1,
        endLine: -1,
        endColumn: -1,
        isPseudo: true
    };
}

export function makeInitialStateSourceLocation():SourceLocation {
    return {
        toString: function () {
            return "-InitialState-";
        },
        file: "",
        beginLine: -1,
        beginColumn: -1,
        endLine: -1,
        endColumn: -1,
        isPseudo: true
    };
}
