(function () {
    function fff(value) {
        return value;
    };
    function iii(obj, jjj) {
        fff(jjj);
        jjj(obj);
        return {BAR: true};
    };
    fff.toString();
    iii.toString();
    function ggg() {
    }

    function hhh() {
    }

    iii({FOO: 42}, ggg);
    iii({}, hhh);
})();
