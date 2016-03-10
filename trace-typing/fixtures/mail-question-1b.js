function f(x) {
    return x.p;
}
function g(x) {
    return x.q;
}
f({p: 3});
g({q: 3});
function c() {
    var h = g;
    h = f;
    h({p: 5}); // BAD,
}
c();
