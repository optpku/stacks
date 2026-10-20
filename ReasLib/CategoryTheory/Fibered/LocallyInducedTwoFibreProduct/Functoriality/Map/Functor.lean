module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom functor for locally induced two-fibre-product maps

The map and modification actions form the hom-category functor between two fixed selected
cospans. This file also exposes its action on isomorphisms.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [Projections.Has (P := P) (Q := Q)]
variable [Q.IsClosedUnderIsomorphisms]
variable [Projections.IsDetected (P := P) (Q := Q)]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ χ : Bicategory.CospanTransform
  (B := Bicategory.LocallyInducedBicategory
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
    (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂}

/-- The locally induced two-fibre-product action preserves identity cospan modifications. -/
@[simp]
theorem map₂.id
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    map₂ (Bicategory.CospanTransform.Hom.id ψ) = 𝟙 (map ψ) := sorry

/-- The locally induced two-fibre-product action preserves vertical composition of cospan
modifications. -/
@[simp]
theorem map₂.comp
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    map₂ (Bicategory.CospanTransform.Hom.comp Γ Δ) =
      map₂ Γ ≫ map₂ Δ := sorry

/-- Explicit locally induced two-fibre-product maps are functorial in transformations and
modifications between each fixed pair of selected cospans. -/
@[stacks 0040 "hom functor of the locally induced two-fibre-product action"]
noncomputable def mapFunctor :
    Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂ ⥤
      (apex F₁ G₁ ⟶ apex F₂ G₂) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The object action of the locally induced two-fibre-product hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    mapFunctor.obj ψ = map ψ := sorry

/-- The morphism action of the locally induced two-fibre-product hom functor is `map₂`. -/
@[simp]
theorem mapFunctor.map
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    mapFunctor.map Γ = map₂ Γ := sorry

/-- An isomorphism of selected cospan transformations induces an isomorphism between the
corresponding locally induced two-fibre-product maps. -/
@[stacks 0040 "isomorphism of locally induced two-fibre-product maps"]
noncomputable def map.iso (e : ψ ≅ φ) :
    map ψ ≅ map φ :=
  mapFunctor.mapIso e

/-- The forward component of an induced locally full map isomorphism is the image of the forward
cospan modification. -/
@[simp]
theorem map.iso.hom (e : ψ ≅ φ) :
    (map.iso e).hom = map₂ e.hom := sorry

/-- The inverse component of an induced locally full map isomorphism is the image of the inverse
cospan modification. -/
@[simp]
theorem map.iso.inv (e : ψ ≅ φ) :
    (map.iso e).inv = map₂ e.inv := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
