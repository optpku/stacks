/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.FamilyPullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v w

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S}
variable {I : Type v} {I' : Type w}
variable {Xᵢ : I → AlgebraicSpace S} {X'ᵢ : I' → AlgebraicSpace S}
variable {f : ∀ i, Xᵢ i ⟶ X} {f' : ∀ i, X'ᵢ i ⟶ X'}
variable {g : X' ⟶ X}

/- Definition 74.22.9: with families `𝒰' = {X'ᵢ ⟶ X'}_{i ∈ I'}`, `𝒰 = {Xᵢ ⟶ X}_{i ∈ I}`,
index map `α : I' → I`, base map `g : X' ⟶ X`, and component maps `gᵢ : X'ᵢ ⟶ X_{α(i)}` as
in Lemma 74.22.8, the functor sending `(Vᵢ, φᵢⱼ)` to
`(gᵢ^* V_{α(i)}, (gᵢ × gⱼ)^* φ_{α(i)α(j)})` constructed there is the pullback functor on
descent data. -/
@[stacks 0ADP] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f ⥤
          AlgebraicGeometry.AlgebraicSpace.DescentData X'ᵢ f')

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom_obj_obj :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f) → (i : I') →
          ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom
              α gᵢ comm).obj D).obj i =
            (AlgebraicGeometry.AlgebraicSpace.overPullback (gᵢ i)).obj (D.obj (α i)))

#check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom_obj_hom :
    (α : I' → I) → (gᵢ : ∀ i, X'ᵢ i ⟶ Xᵢ (α i)) →
      (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g) →
        (D : AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f) →
          {Z : AlgebraicSpace S} → (q : Z ⟶ X') → {i j : I'} →
            (h₀ : Z ⟶ X'ᵢ i) → (h₁ : Z ⟶ X'ᵢ j) →
              (hh₀ : h₀ ≫ f' i = q) → (hh₁ : h₁ ≫ f' j = q) →
                ((AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functorOfHom
                    α gᵢ comm).obj D).hom q h₀ h₁ hh₀ hh₁ =
                  Pseudofunctor.DescentData.pullFunctorObjHom
                    (F := AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S)
                    (f := f) (p := g) (f' := f') (α := α) (p' := gᵢ) (w := comm)
                    D q h₀ h₁ hh₀ hh₁)
