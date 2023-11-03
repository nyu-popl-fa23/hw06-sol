const plus = x => y => x + y;

console.log( plus(3)(4) );

const forloop =
  body =>
    function reduce(n) {
      return acc => n === 0 ? acc : body(n)(reduce(n - 1)(acc))
    };

const factorial =
  n => forloop(i => acc => i * acc)(n)(1);

console.log( factorial(4) );
console.log( factorial(5) );
