const fix = 
  f =>
    (x => f(y => (x(x))(y)))(x => f(y => (x(x))(y)));

const facFun = 
  factorial =>
    n => n > 1 ? n * factorial(n-1) : 1;

const factorial = fix(facFun);

console.log( factorial(4) );
console.log( factorial(5) );