module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Contractible
public import ReasLib.Algebra.Category.DifferentialGraded.DirectSum
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Admissibly monic factorizations

Using a cone on an identity and a binary biproduct, every closed morphism factors through an
admissibly monic map followed by a split homotopy equivalence.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasBinaryBiproducts (Comp R A)]

/-- An explicit cone on the source identity yields an admissibly monic factorization of a
closed morphism. -/
theorem exists_admissibleMonoFactorization
    {x y : Comp R A} (C : B.AdmissibleCone (𝟙 x)) (α : x ⟶ y) :
    ∃ (y' : Comp R A) (i : x ⟶ y') (r : HomotopyRetract y' y),
      Comp.IsAdmissibleMono i ∧ i ≫ r.projection = α := sorry

end DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCone

namespace DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable {B : CompBoundaryAssignment R A}
variable [HasBinaryBiproducts (Comp R A)]

/-- Lemma 22.27.6 (09QM): every closed morphism factors through an admissibly monic map and
a homotopy-retract projection. The cone family is explicit because it is observable data. -/
@[stacks 09QM]
theorem exists_admissibleMonoFactorization (C : B.AdmissibleCones)
    {x y : Comp R A} (α : x ⟶ y) :
    ∃ (y' : Comp R A) (i : x ⟶ y') (r : HomotopyRetract y' y),
      Comp.IsAdmissibleMono i ∧ i ≫ r.projection = α := sorry

end DifferentialGradedCategory.CompBoundaryAssignment.AdmissibleCones
