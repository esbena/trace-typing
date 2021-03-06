console.log("XXX: 6");
var Lazy = require('lazy.js');

function getBigArrayOfPeople() {
    return [
        {name: 'Smithson', lastName: 'Smith'},
        {name: 'X', lastName: 'Y'},
        {name: 'Y', lastName: 'X'},
        {name: 'Z', lastName: 'Z'},
    ];
}

var people = getBigArrayOfPeople();

var results = [];
for (var i = 0; i < people.length; ++i) {
    var lastName = people[i].lastName;
    if (lastName.startsWith('Smith')) {
        results.push(people[i]);
        if (results.length === 5) {
            break;
        }
    }
}

var result = Lazy(people)
    .pluck('lastName')
    .filter(function (name) {
        return name.startsWith('Smith');
    })
    .take(5);

var uniqueRandsFrom1To1000 = Lazy.generate(Math.random)
    .map(function (e) {
        return Math.floor(e * 1000) + 1;
    })
    .uniq()
    .take(300);

var fibonacci = Lazy.generate(function () {
    var x = 1,
        y = 1;
    return function () {
        var prev = x;
        x = y;
        y += prev;
        return prev;
    };
}());

// Output: undefined
var length = fibonacci.length();

// Output: [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
fibonacci.take(10).toArray();

function inc(i) {
    return i++;
}

function isEven(i) {
    return i % 2 === 0;
}

var asyncSequence = Lazy(people)
    .async(100) // specifies a 100-millisecond interval between each element
    .map(inc)
    .filter(isEven)
    .take(20);

// This function returns immediately and begins iterating over the sequence asynchronously.
asyncSequence.each(function (e) {
    console.log(new Date().getMilliseconds() + ": " + e);
});

var text = 'Lorem ipsum dolor sit amet, consectetuer adipiscing elit, sed diam nonummy nibh euismod tincidunt ut \n' +
    'laoreet dolore magna aliquam erat volutpat. Ut wisi enim ad minim veniam, quis nostrud exerci tation ullamcorper  \n' +
    'suscipit lobortis nisl ut aliquip ex ea commodo consequat. Duis autem vel eum iriure dolor in hendrerit in  \n' +
    'vulputate velit esse molestie consequat, vel illum dolore eu feugiat nulla facilisis at vero eros et accumsan  \n' +
    'et iusto odio dignissim qui blandit praesent luptatum zzril delenit augue duis dolore te feugait nulla facilisi. \n' +
    ' Nam liber tempor cum soluta nobis eleifend option congue nihil imperdiet doming id quod mazim placerat facer possim assum. \n' +
    ' Typi non habent claritatem insitam; est usus legentis in iis qui facit eorum claritatem. Investigationes demonstraverunt lectores';
var firstFiveLines = text.split("\n").slice(0, 5);

var firstFiveLines = Lazy(text).split("\n").take(5);

var firstFiveWords = Lazy(text).match(/[a-z0-9]+/i).take(5);
