module

public import ReasLib.Algebra.Group.Prod.Exact
import StacksCheckRecall

/-!
# The endpoint-unit difference sequence

@stack 00JG

The multiplicative endpoint ratio from Example 10.55.5 is the additive coordinate-difference
map on `Additive kˣ`.  The reusable construction and its exactness live in ReasLib.
-/

@[expose] public section

@[stacks 00JG]
#check @MonoidHom.sndDivFst

@[stacks 00JG]
#check @MonoidHom.diagonal

@[stacks 00JG]
#check @MonoidHom.sndDivFst_surjective

@[stacks 00JG]
#check @MonoidHom.toAdditive_diagonal_range_eq_sndDivFst_ker
