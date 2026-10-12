/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map

/-!
# Naturality for maps of explicit two-fibre products

This leaf exposes ordinary naturality of the `2`-cell action on maps of
property-selected explicit two-fibre products.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

section Functoriality

variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ : CospanTransform F₁ G₁ F₂ G₂}

/-- The `2`-morphism induced by a cospan modification is natural in explicit two-fibre-product
morphisms. -/
@[reassoc]
theorem map₂.naturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    {A B : (BasedCategory.PseudoPullback F₁.hom G₁.hom).obj} (f : A ⟶ B) :
    (map ψ).hom.toFunctor.map f ≫ (map₂ Γ).hom.toNatTrans.app B =
      (map₂ Γ).hom.toNatTrans.app A ≫ (map φ).hom.toFunctor.map f := sorry

/-- Two induced full-subbicategory `2`-morphisms agree when all of their explicit
pseudo-pullback components agree. -/
theorem map₂.ext
    {Γ Δ : Pseudofunctor.StrongTrans.Hom ψ φ}
    (h : ∀ A : (BasedCategory.PseudoPullback F₁.hom G₁.hom).obj,
      (map₂ Γ).hom.toNatTrans.app A = (map₂ Δ).hom.toNatTrans.app A) :
    map₂ Γ = map₂ Δ := sorry

end Functoriality

end TwoFibreProduct

end CategoryTheory
