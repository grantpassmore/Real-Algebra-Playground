muchnik.py
========
Quantifier elimination for real and complex numbers

Requirements:

* [blist](https://pypi.python.org/pypi/blist/)

Usage
---------
Construct a Muchniker object (from algebra such `SympyWrapper`):

    muchniker = muchnik.Muchniker(algebra)

* Eliminate existential quantifier for complex numbers where `equalities` is a list of equalities and `inequalities` is a list of inequalities:

        muchniker.complex_full(equalities, inequalities)
* Eliminate existential quantifier for real numbers where `lesser` is a list of polynomials that must be less than zero, `equalities` is a list of equalities and `greater` is a list of polynomials that must be greater than zero:

        muchniker.real_full(lesser, equalities, greater)

Both `complex_full` and `real_full` print all the suitable diagrams and whether formula is satisfiable or unsatisfiable.

Examples:
---------------

    muchniker.complex_full([x-y, x-1], [])
    muchniker.real_full([x-y], [x-1], [])

Returns:
------------

Complex:
<pre>
[      
  ([-y, -y + 1, y - 1], []), 
  ([-y, y - 1], [-y + 1]), 
  ([-y + 1, y - 1], [-y]), 
  ([y - 1], [-y, -y + 1])
]
</pre>
Corresponds to a formula in DNF:
<pre>
-y == 0 /\ -y + 1 == 0 /\ y - 1 == 0 \/ 
-y == 0 /\ -y + 1  != 0 /\ y - 1 == 0 \/ 
-y  != 0 /\ -y + 1 == 0 /\ y - 1 == 0 \/ 
-y  != 0 /\ -y + 1  != 0 /\ y - 1 == 0
</pre>

Reals:
<pre>
[([-y, -y + 1], [], [y - 1]),
([-y], [-y + 1], [y - 1]),
([-y], [], [-y + 1, y - 1]),
([-y + 1], [-y], [y - 1]),
([], [-y, -y + 1], [y - 1]),
([], [-y], [-y + 1, y - 1]),
([-y + 1], [], [-y, y - 1]),
([], [-y + 1], [-y, y - 1]),
([], [], [-y, -y + 1, y - 1])]
</pre>

Corresponds to a formula in DNF: 
<pre>
-y < 0 /\ -y + 1 < 0 /\ y - 1 > 0 \/
-y < 0 /\ -y + 1 = 0 /\ y - 1 > 0 \/
-y < 0 /\ -y + 1 > 0 /\ y - 1 > 0 \/
...
-y > 0 /\ -y + 1 > 0 /\ y - 1 > 0

</pre>

Source
---------
Ch 2.1, 2.2 from [Combined Decision Procedures for Nonlinear Arithmetics, Real and Complex](http://www.cl.cam.ac.uk/~gp351/passmore-phd-thesis.pdf)

cohenhorm.py
========
Quantifier elimination for reals

Requirements:

* [blist](https://pypi.python.org/pypi/blist/)

Usage
---------
Construct a CohenHormander object (from algebra such `SympyWrapper`):

    cohenhormander = cohenhorm.CohenHormander(algebra)

* Eliminate existential quantifier for real numbers where `lesser` is a list of polynomials that must be less than zero, `equalities` is a list of equalities and `greater` is a list of polynomials that must be greater than zero:

        cohenhormander.real_full(lesser, equalities, greater)

`real_full` also print suitable diagrams and assignments.

Examples:
---------------

    cohenhormander.real_full([x-y], [x-1], [])

Returns:
------------

Same as muchnik

Source
---------
Follows theory part of [Real quantiﬁer elimination](http://gc83.perso.sfr.fr/M2/harrison-real.pdf)

sympywrapper.py
=============
Sympy Wrapper for algebraic operations

Requirements:

* [sympy](http://docs.sympy.org/latest/index.html)

Usage
---------
Construct a variable `x`:

    x = sympy.var('x')

Construct an algebra that can be used to eliminate variable `x`:

    algebra = sympywrapper.SympyWrapper('x')

Construct a polynomial in `x`, `y`, `z`:

    x**2 + 3*y*x + z - 7