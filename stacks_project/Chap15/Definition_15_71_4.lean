/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.71.4: ideal-projective modules

The root invariant is the ideal `Module.projectiveFactorIdeal R M`; ideal-projectivity is an
ideal inclusion, not a typeclass.

@stack 0G93
-/

universe u v

/- Definition 15.71.4: every scalar action indexed by `I` factors through a projective module. -/
@[stacks 0G93]
#check fun (R : Type u) [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] => Module.IsIdealProjective I M

/- The stronger ideal-valued owner. -/
#check @Module.projectiveFactorIdeal

/- Pointwise access to the defining factorisations. -/
#check @Module.isIdealProjective_iff

/- Projectivity is exactly ideal-projectivity for the top ideal. -/
#check @Module.IsIdealProjective.top_iff

/- Ideal-valued form of the top criterion. -/
#check @Module.projectiveFactorIdeal.eq_top_iff
