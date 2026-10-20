module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FormalSmooth
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite extension stability of solutions

The source-facing finite-tower stability statement for the solution predicate lives here so that
later developments can use it without importing a chapter implementation.

@stack 0GLR
-/

universe u v w x y z

namespace IsSolutionFor

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra A K2] [Algebra K K2] [Algebra K1 K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2] [FiniteDimensional K K2]

/-- Lemma 15.117.1: a solution `K₁ / K` remains a solution after any finite extension
`K₂ / K₁`, viewed as an extension of `K`. -/
@[stacks 0GLR "Lemma 15.117.1: finite extension stability of solutions"]
theorem of_finite_extension (hK1 : IsSolutionFor A B K L K1) :
    IsSolutionFor A B K L K2 := sorry
-- Proof strategy: rewrite the goal and `hK1` with `IsSolutionFor.iff_forall_ideals`.  Contract a
-- chosen pair of maximal branches for the `K2` normalizations along the canonical integral-closure
-- and reduced-tensor tower maps to maximal branches for `K1`; the tower square supplies the
-- lies-over relation.  Apply `hK1` on the contracted branches, then use
-- `DVR.Field.BaseChange.formallySmoothAt` for the finite extension `K2 / K1` and transport formal
-- smoothness across the canonical localization comparisons to the original `K2` branches.

end

end IsSolutionFor

end
