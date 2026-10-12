/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Compact
import StacksCheckRecall

/-!
# Proposition 15.79.3 (07LT)

@stack 07LT

The reusable equivalence between perfect and compact objects of `D(R)` is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Perfect.Compact`.
-/

@[expose] public section

open CategoryTheory

/- Proposition 15.79.3 (07LT): for a ring `R` and `K : DerivedCategory (ModuleCat R)`, the
object `K` is perfect if and only if it is compact. -/
@[stacks 07LT "perfect complexes are compact"]
#check @DerivedCategory.isPerfect_iff_isCompactObject
