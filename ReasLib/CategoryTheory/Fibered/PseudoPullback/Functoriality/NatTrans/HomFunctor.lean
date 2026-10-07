module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.Modification
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Postcomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-functor API for explicit pseudo-pullbacks

This leaf packages the modification action as the functor on each hom category of based cospans,
and supplies its isomorphism and component computation API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- Explicit pseudo-pullback maps are functorial in transformations and modifications between
each fixed pair of based cospans. -/
@[stacks 0040 "hom functor of the explicit pseudo-pullback cospan action"]
def mapFunctor :
    BasedCospanTransform F₁ G₁ F₂ G₂ ⥤
      (PseudoPullback F₁ G₁ ⥤ᵇ PseudoPullback F₂ G₂) where
  obj := CategoryTheory.BasedCategory.PseudoPullback.map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The object action of the explicit pseudo-pullback hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    mapFunctor.obj ψ = CategoryTheory.BasedCategory.PseudoPullback.map ψ := sorry

/-- The morphism action of the explicit pseudo-pullback hom functor is `map₂`. -/
@[simp]
theorem mapFunctor.map
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    mapFunctor.map Γ = map₂ Γ := sorry

/-- An isomorphism of cospan transformations induces an isomorphism between the corresponding
explicit pseudo-pullback maps. -/
@[stacks 0040 "isomorphism of explicit pseudo-pullback maps induced by a cospan isomorphism"]
def map.iso
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (e : ψ ≅ φ) :
    CategoryTheory.BasedCategory.PseudoPullback.map ψ ≅
      CategoryTheory.BasedCategory.PseudoPullback.map φ :=
  mapFunctor.mapIso e

/-- The forward component of an induced pseudo-pullback map isomorphism is `map₂` of the forward
cospan modification. -/
@[simp]
theorem map.iso.hom
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (e : ψ ≅ φ) :
    (map.iso e).hom = map₂ e.hom := sorry

/-- The inverse component of an induced pseudo-pullback map isomorphism is `map₂` of the inverse
cospan modification. -/
@[simp]
theorem map.iso.inv
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (e : ψ ≅ φ) :
    (map.iso e).inv = map₂ e.inv := sorry

/-- The first-projection comparisons, natural in the cospan transformation.  The source varies
the induced pseudo-pullback map, while the target varies the left endpoint map. -/
@[stacks 0040 "natural first-projection comparison for explicit pseudo-pullback maps"]
def map.fstNatIso :
    mapFunctor ⋙
        BasedCategory.postcomposition (PseudoPullback F₁ G₁) (PseudoPullback.fst F₂ G₂) ≅
      BasedCospanTransform.leftFunctor ⋙
        BasedCategory.precomposition X₂ (PseudoPullback.fst F₁ G₁) :=
  NatIso.ofComponents map.fstIso map₂.fstCommutes

/-- The forward component of `map.fstNatIso` is the canonical first-projection comparison. -/
@[simp]
theorem map.fstNatIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.hom.app ψ = (map.fstIso ψ).hom := sorry

/-- The inverse component of `map.fstNatIso` is the inverse first-projection comparison. -/
@[simp]
theorem map.fstNatIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.inv.app ψ = (map.fstIso ψ).inv := sorry

/-- The second-projection comparisons, natural in the cospan transformation.  The source varies
the induced pseudo-pullback map, while the target varies the right endpoint map. -/
@[stacks 0040 "natural second-projection comparison for explicit pseudo-pullback maps"]
def map.sndNatIso :
    mapFunctor ⋙
        BasedCategory.postcomposition (PseudoPullback F₁ G₁) (PseudoPullback.snd F₂ G₂) ≅
      BasedCospanTransform.rightFunctor ⋙
        BasedCategory.precomposition Y₂ (PseudoPullback.snd F₁ G₁) :=
  NatIso.ofComponents map.sndIso map₂.sndCommutes

/-- The forward component of `map.sndNatIso` is the canonical second-projection comparison. -/
@[simp]
theorem map.sndNatIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.hom.app ψ = (map.sndIso ψ).hom := sorry

/-- The inverse component of `map.sndNatIso` is the inverse second-projection comparison. -/
@[simp]
theorem map.sndNatIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.inv.app ψ = (map.sndIso ψ).inv := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
