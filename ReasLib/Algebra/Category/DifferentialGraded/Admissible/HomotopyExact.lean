module

public import ReasLib.Algebra.Category.DifferentialGraded.Admissible.Strictification
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homotopy exactness of a graded split sequence

A map into the middle term which is null after the quotient, followed by a map which is null on
the subobject, has null-homotopic composite.
-/

open CategoryTheory

universe u v w

namespace CategoryTheory.ShortComplex.GradedSplitting

open DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable {S : ShortComplex (Comp R A)}

/-- Strict boundary vanishing around a graded splitting forces the middle composite to vanish. -/
theorem comp_eq_zero (sigma : S.GradedSplitting)
    {W Z : Comp R A} {b : W ⟶ S.X₂} {b' : S.X₂ ⟶ Z}
    (right : b ≫ S.g = 0) (left : S.f ≫ b' = 0) :
    b ≫ b' = 0 := sorry

/-- Lemma 22.27.8 (09QP): null-homotopic boundary composites around a graded split sequence
force the middle composite to be null-homotopic. -/
@[stacks 09QP]
theorem homotopic_comp_zero (sigma : S.GradedSplitting)
    {W Z : Comp R A} {b : W ⟶ S.X₂} {b' : S.X₂ ⟶ Z}
    (right : Homotopic W.obj S.X₃.obj (b ≫ S.g) 0)
    (left : Homotopic S.X₁.obj Z.obj (S.f ≫ b') 0) :
    Homotopic W.obj Z.obj (b ≫ b') 0 := sorry

end CategoryTheory.ShortComplex.GradedSplitting
