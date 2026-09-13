# Tree examples the user did NOT select, for the running example (Figure 3).
# Each line is `example TOP BOT INDEX`: the pattern with production TOP at the root and
# production BOT nested at child position INDEX.  Production identifiers are the indices
# printed by `greta cfg2ta`; INDEX counts every right-hand-side element, terminals
# included (the `t_idx` of Section 3).
#
# Fig. 3a: the rejected tree has (PLUS,3) as its right child, so PLUS is left-associative.
example 5 5 2
# Fig. 3b: likewise for (STAR,3).
example 6 6 2
# Fig. 3c: the rejected tree has (STAR,3) above (PLUS,3), so STAR binds tighter.
example 6 5 0
# Fig. 3d: the rejected tree has (IF,6) above (IF,4), so `else` binds to the nearest `if`.
example 2 1 3
