/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Moving

@[expose] public section

universe u

namespace AlgebraicGeometry.CycleGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- On a nonsingular quasi-projective variety, every cycle is rationally equivalent to one
that intersects a given cycle properly. -/
theorem existsRationallyEquivalentIntersectProperly_of_quasiProjective
    (X : SchemeOverField k) [QuasiProjectiveVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (β : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s) :
    ∃ α' : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r,
      RationalEquivalence.RationallyEquivalent
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α' α ∧
        AlgebraicCycle.IntersectProperly
          (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α')
          (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β) := sorry

end AlgebraicGeometry.CycleGroup
