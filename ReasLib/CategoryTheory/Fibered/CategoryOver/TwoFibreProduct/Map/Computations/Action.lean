module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Action computations for two-fibre-product maps of fibred categories

This leaf records the object and `2`-morphism action of the application-facing
`FiberedCategoryOver.TwoFibreProduct` map construction, together with its identity and
composition computations.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

variable {ψ φ χ : CospanTransform F₁ G₁ F₂ G₂}

/-- The underlying based functor of the application-facing map is the explicit
pseudo-pullback map. -/
@[simp]
theorem map.obj (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map ψ).obj =
      BasedCategory.PseudoPullback.map
        (LocallyInduced.TwoFibreProduct.CospanTransform.forget ψ) := sorry

/-- The base component of an application-facing two-fibre-product `2`-morphism is the
identity. -/
@[simp]
theorem map₂.base
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.baseMap ((map₂ Γ).hom.toNatTrans.app A) =
      𝟙 (BasedCategory.PseudoPullback.baseObj A) := sorry

/-- The first component of an application-facing two-fibre-product `2`-morphism is the left
component of the cospan modification. -/
@[simp]
theorem map₂.fst
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.fstMap ((map₂ Γ).hom.toNatTrans.app A) =
      (Bicategory.CospanTransform.Hom.left Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.fstObj A) := sorry

/-- The second component of an application-facing two-fibre-product `2`-morphism is the right
component of the cospan modification. -/
@[simp]
theorem map₂.snd
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (A : (BasedCategory.PseudoPullback F₁.obj G₁.obj).obj) :
    BasedCategory.PseudoPullback.sndMap ((map₂ Γ).hom.toNatTrans.app A) =
      (Bicategory.CospanTransform.Hom.right Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.sndObj A) := sorry

/-- The object action of the application-facing hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    mapFunctor.obj ψ = map ψ := sorry

/-- The morphism action of the application-facing hom functor is `map₂`. The heterogeneous
equality absorbs the dependent endpoint transport in the two hom categories. -/
theorem mapFunctor.map
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    mapFunctor.map Γ ≍ map₂ Γ := sorry

/-- The forward morphism of an induced map isomorphism is the image of its forward cospan
modification, up to the dependent endpoint transport. -/
theorem map.iso.hom (e : ψ ≅ φ) :
    (map.iso e).hom ≍ map₂ e.hom := sorry

/-- The inverse morphism of an induced map isomorphism is the image of its inverse cospan
modification, up to the dependent endpoint transport. -/
theorem map.iso.inv (e : ψ ≅ φ) :
    (map.iso e).inv ≍ map₂ e.inv := sorry

/-- The map induced by the identity cospan transformation is the identity. -/
@[simp]
theorem map.id (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (Bicategory.CospanTransform.id F G) = 𝟙 (apex F G) := sorry

/-- Maps of application-facing two-fibre products preserve composition of cospan
transformations. -/
@[simp]
theorem map.comp
    {X₃ Y₃ S₃ :
      FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (φ : CospanTransform F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) = map ψ ≫ map φ := sorry

/-- Two-fibre-product mapping preserves identity modifications, up to the dependent endpoint
transport of the application-facing facade. -/
theorem map₂.id (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map₂ (CospanTransform.Hom.id ψ) ≍ 𝟙 (map ψ) := sorry

/-- Two-fibre-product mapping preserves vertical composition of modifications, up to the
dependent endpoint transport of the application-facing facade. -/
theorem map₂.comp
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    map₂ (CospanTransform.Hom.comp Γ Δ) ≍ map₂ Γ ≫ map₂ Δ := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
