function f(x) {
    return x.p;
}
function g(x) {
    return x.q;
}
f({p: 3});
g({q: 3});
function c(b) {
    var h = b ? f : g;
    h({p: 5}); // BAD,
}
c(true);
c(false);
