/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of two-fibre products of fibred categories

This leaf owns the application-facing map, `2`-cell, local Hom functor, and canonical
isomorphisms associated to maps of cospans.  Computation lemmas are kept in the sibling
`Map.Computations` leaves.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

variable {ψ φ : CospanTransform F₁ G₁ F₂ G₂}

/-- The componentwise map between explicit two-fibre-product carriers. -/
@[stacks 02XQ "functorial map"]
noncomputable abbrev map (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    apex F₁ G₁ ⟶ apex F₂ G₂ :=
  LocallyInduced.TwoFibreProduct.map
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) ψ

/-- A modification of cospan transformations induces the corresponding `2`-morphism of
application-facing two-fibre-product maps.

This facade is opaque so elaborating its computation API does not repeatedly unfold the complete
locally induced endpoint construction. The `map₂.base`, `map₂.fst`, and `map₂.snd` theorems form
its application-facing reduction interface; the neutral `LocallyInduced.TwoFibreProduct.map₂`
owner supplies full underlying/naturality/extensionality API. -/
@[stacks 0040 "modification action on two-fibre-product maps of fibred categories"]
noncomputable def map₂ (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map ψ ⟶ map φ :=
  LocallyInduced.TwoFibreProduct.map₂
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) Γ

/-- The action on transformations and modifications between fixed cospans, bundled as a
functor between hom categories. -/
@[stacks 0040 "hom functor of two-fibre-products of fibred categories"]
noncomputable abbrev mapFunctor :
    CospanTransform F₁ G₁ F₂ G₂ ⥤ (apex F₁ G₁ ⟶ apex F₂ G₂) :=
  LocallyInduced.TwoFibreProduct.mapFunctor
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C)

/-- An isomorphism of cospan transformations induces an isomorphism of their
application-facing two-fibre-product maps. -/
@[stacks 0040 "isomorphism of two-fibre-product maps of fibred categories"]
noncomputable abbrev map.iso (e : ψ ≅ φ) :
    map ψ ≅ map φ :=
  mapFunctor.mapIso e

/-- The induced map commutes with the first projection up to the canonical invertible
`2`-cell. -/
@[stacks 0040 "first projection comparison for a two-fibre-product map of fibred categories"]
noncomputable abbrev map.fstIso (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map ψ ≫ fst F₂ G₂ ≅ fst F₁ G₁ ≫ ψ.left :=
  LocallyInduced.TwoFibreProduct.map.fstIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) ψ

/-- The induced map commutes with the second projection up to the canonical invertible
`2`-cell. -/
@[stacks 0040 "second projection comparison for a two-fibre-product map of fibred categories"]
noncomputable abbrev map.sndIso (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map ψ ≫ snd F₂ G₂ ≅ snd F₁ G₁ ≫ ψ.right :=
  LocallyInduced.TwoFibreProduct.map.sndIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) ψ

/-- The first-projection comparisons, natural in cospan transformations of fibred categories. -/
@[stacks 0040 "natural first-projection comparison for two-fibre-products of fibred categories"]
noncomputable def map.fstNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (fst F₂ G₂) ≅
      Bicategory.CospanTransform.leftFunctor ⋙
        Bicategory.precomp X₂ (fst F₁ G₁) :=
  LocallyInduced.TwoFibreProduct.map.fstNatIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C)

/-- The second-projection comparisons, natural in cospan transformations of fibred
categories. -/
@[stacks 0040 "natural second-projection comparison for two-fibre-products of fibred categories"]
noncomputable def map.sndNatIso :
    mapFunctor ⋙ Bicategory.postcomp (apex F₁ G₁) (snd F₂ G₂) ≅
      Bicategory.CospanTransform.rightFunctor ⋙
        Bicategory.precomp Y₂ (snd F₁ G₁) :=
  LocallyInduced.TwoFibreProduct.map.sndNatIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C)

/-- The comparison between the two target legs after applying a map of application-facing
two-fibre products. -/
@[stacks 0040 "target comparison for a two-fibre-product map of fibred categories"]
noncomputable abbrev map.comparisonIso
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map ψ ≫ fst F₂ G₂) ≫ F₂ ≅ (map ψ ≫ snd F₂ G₂) ≫ G₂ :=
  LocallyInduced.TwoFibreProduct.map.comparisonIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) ψ

/-- The canonical invertible identity comparison for application-facing two-fibre-product
maps. -/
@[stacks 0040 "identity comparison for two-fibre-product maps of fibred categories"]
noncomputable abbrev map.idIso (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (Bicategory.CospanTransform.id F G) ≅ 𝟙 (apex F G) :=
  LocallyInduced.TwoFibreProduct.map.idIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The canonical invertible composition comparison for application-facing two-fibre-product
maps. -/
@[stacks 0040 "composition comparison for two-fibre-product maps of fibred categories"]
noncomputable abbrev map.compIso
    {X₃ Y₃ S₃ :
      FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (φ : CospanTransform F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) ≅ map ψ ≫ map φ :=
  LocallyInduced.TwoFibreProduct.map.compIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) ψ φ

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
