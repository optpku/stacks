module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Split Distinguished Triangles

@stack 05QT

This leaf records the elementary split-triangle consequences that are not
already packaged by Mathlib's binary-biproduct triangle API.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Pretriangulated.SplitTriangle

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [CategoryTheory.Pretriangulated D]

/-- Lemma 13.4.11 (1): the second morphism of a distinguished triangle is split epic when its
third morphism vanishes. -/
@[stacks 05QT]
theorem isSplitEpi₂_of_mor₃_eq_zero {T : CategoryTheory.Pretriangulated.Triangle D}
    (hT : T ∈ distTriang D) (hzero : T.mor₃ = 0) :
    IsSplitEpi T.mor₂ := sorry

/-- Lemma 13.4.11 (2): a chosen right inverse to the second morphism of a distinguished triangle
gives the canonical biproduct isomorphism from its first and third vertices. -/
@[stacks 05QT]
theorem isIso_biprodDesc_of_rightInverse₂ {T : CategoryTheory.Pretriangulated.Triangle D}
    (hT : T ∈ distTriang D) (s : T.obj₃ ⟶ T.obj₂) (hs : s ≫ T.mor₂ = 𝟙 T.obj₃) :
    IsIso (biprod.desc T.mor₁ s) := sorry

end CategoryTheory.Pretriangulated.SplitTriangle
