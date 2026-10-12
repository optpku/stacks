/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module Support Dimension under Surjective Scalar Maps

This leaf records the support-dimension part of restriction of scalars along a
surjective algebra map.  It is independent of locality, Noetherianity, and
module finiteness.
-/

@[expose] public section

universe u v w

namespace Module

/-- Restricting scalars along a surjective algebra map preserves module support
dimension. -/
@[stacks 0AAD "support dimension under a surjection"]
theorem supportDim_restrictScalars_eq_of_surjective
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (hsurj : Function.Surjective (algebraMap R S)) :
    supportDim R N = supportDim S N := sorry

end Module
