module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Postcomposition of Homological Functors

This leaf records the target-side operation on homological functors. The
source-side operation along a triangulated functor is already owned by Mathlib.
-/

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable {A' : Type u₃} [Category.{v₃} A'] [Abelian A']

/-- Lemma 13.4.20: postcomposition by an exact functor between abelian categories
preserves homological functors. -/
@[stacks 05QZ]
instance isHomological_comp_exact (H : D ⥤ A) (G : A ⥤ₑ A') [H.IsHomological] :
    (H ⋙ G.obj).IsHomological := sorry

end

end CategoryTheory.Functor
