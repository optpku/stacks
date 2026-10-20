module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.Exactness
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Selected-Coproduct Telescope Triangles

@stack 094A

This file specializes the presentation-level image comparison to a telescope
triangle built from the coproduct selected by a `HasCoproduct` instance.  It
does not introduce a second comparison morphism: every statement refers
directly to `Presentation.imageComparison`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory.HomotopyColimit.SelectedCoproduct

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]
variable {K : ℕ ⥤ D} [HasCoproduct K.obj] {X : D}

/-- For a selected-coproduct telescope triangle, the generic image comparison restricts
to the image of each selected coproduct inclusion followed by the triangle's second map. -/
@[simp, reassoc, stacks 0CRK]
theorem colimit_ι_comp_imageComparison (H : D ⥤ A) (toCocone : ∐ K.obj ⟶ X)
    (connecting : X ⟶ (∐ K.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap K)
      toCocone connecting ∈ distTriang D)
    [HasColimit (K ⋙ H)] (n : ℕ) :
    colimit.ι (K ⋙ H) n ≫
        Presentation.imageComparison
          (Presentation.ofCoproductTriangle toCocone connecting h_triangle) H =
      H.map (Limits.Sigma.ι K.obj n ≫ toCocone) := sorry

namespace PreadditiveCoyoneda

namespace ImageComparison

/-- The representable generic image comparison is an isomorphism when the representable
functor preserves the coproduct of the particular input sequence. -/
theorem isIso (K₀ : D) {L : ℕ ⥤ D} [HasCoproduct L.obj] {Lhocolim : D}
    [PreservesColimit (Discrete.functor L.obj) (preadditiveCoyoneda.obj (op K₀))]
    (toCocone : ∐ L.obj ⟶ Lhocolim)
    (connecting : Lhocolim ⟶ (∐ L.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap L)
      toCocone connecting ∈ distTriang D) :
    IsIso (Presentation.imageComparison
      (Presentation.ofCoproductTriangle toCocone connecting h_triangle)
      (preadditiveCoyoneda.obj (op K₀))) := sorry

end ImageComparison

/-- Stacks 094A, Lemma 13.33.9: when `Hom_D(K₀, -)` preserves countable coproducts,
the generic image comparison of any selected-coproduct telescope triangle is an isomorphism. -/
@[stacks 094A]
theorem imageComparison_isIso (K₀ : D)
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K₀))]
    {L : ℕ ⥤ D} [HasCoproduct L.obj] {Lhocolim : D}
    (toCocone : ∐ L.obj ⟶ Lhocolim)
    (connecting : Lhocolim ⟶ (∐ L.obj)⟦(1 : ℤ)⟧)
    (h_triangle : Triangle.mk (Limits.Sequential.telescopeMap L)
      toCocone connecting ∈ distTriang D) :
    IsIso (Presentation.imageComparison
      (Presentation.ofCoproductTriangle toCocone connecting h_triangle)
      (preadditiveCoyoneda.obj (op K₀))) := sorry

end PreadditiveCoyoneda

end CategoryTheory.HomotopyColimit.SelectedCoproduct

end
