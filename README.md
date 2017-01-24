# Closed Rational Polyhedra based on CLP(Q)

This module implements a (rational, closed) polyhedra manipulation
library based on CLP(Q) operations.

The algorithms for the convex hull and project operations are based on
the paper:
```
"Computing convex hulls with a linear solver", Florence Benoy, Andy
King, Frédéric Mesnard.  TPLP 5(1-2): 259-271 (2005).
```

This implementation is guaranteed to work for closed polyhedra
(containing only non-strict inequalities).

See the `poly_clpq.pl` module documentation for usage.


