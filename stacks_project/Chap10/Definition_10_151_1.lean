module

public import ReasLib.RingTheory.Unramified.Basic
import StacksCheckRecall

@[expose] public section

/-!
@stack 00UT
-/

/- Definition 10.151.1 (Stacks tag `00UT`) is owned by the neutral reusable API:
`Algebra.GUnramified` for the finite-presentation refinement of unramifiedness,
`Algebra.UnramifiedAt` and `Algebra.GUnramifiedAt` for its basic-open local forms, and Mathlib's
`Algebra.IsUnramifiedAt` for the canonical stalkwise predicate. -/
#check @Algebra.Unramified
@[stacks 00UT]
#check @Algebra.GUnramified
#check @RingHom.GUnramified
#check @RingHom.unramified_algebraMap
#check @RingHom.gUnramified_algebraMap
@[stacks 00UT]
#check @Algebra.UnramifiedAt
@[stacks 00UT]
#check @Algebra.GUnramifiedAt
#check @Algebra.UnramifiedAt.iff_exists_away
#check @Algebra.GUnramifiedAt.iff_exists_away
#check @Algebra.UnramifiedAt.iff_isUnramifiedAt
#check @Algebra.GUnramifiedAt.iff_isUnramifiedAt
