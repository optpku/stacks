/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity coherence for explicit pseudo-pullback maps

This leaf owns the objectwise and based natural isomorphisms witnessing preservation of identity
cospan transformations by the explicit pseudo-pullback map construction.
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

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}

/-- The identity component maps respect the comparison stored by an object of the
pseudo-pullback. -/
theorem mapId.component.comm
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    CommSq
      (F.toFunctor.map (𝟙 (fstObj P)))
      (comparison
        ((map (BasedCospanTransform.id F G)).obj P))
      (comparison P)
      (G.toFunctor.map (𝟙 (sndObj P))) := sorry

/-- The identity first-component map lies over the identity common-base map. -/
theorem mapId.component.fst.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    X₁.p.IsHomLift (𝟙 (baseObj P)) (𝟙 (fstObj P)) := sorry

/-- The identity second-component map lies over the identity common-base map. -/
theorem mapId.component.snd.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    Y₁.p.IsHomLift (𝟙 (baseObj P)) (𝟙 (sndObj P)) := sorry

/-- The objectwise identity-comparison isomorphism for the explicit pseudo-pullback action.
Its base, first, and second component isomorphisms are identities; only compatibility with the
stored comparison is proof-valued. -/
noncomputable def mapId.component
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (map (BasedCospanTransform.id F G)).obj P ≅ P :=
  mkIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hom_fst := mapId.component.fst.isHomLift F G P)
    (hom_snd := mapId.component.snd.isHomLift F G P)
    (mapId.component.comm F G P)

/-- The base component of the forward identity comparison is the identity. -/
@[simp]
theorem mapId.component.hom.base
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    baseMap (mapId.component F G P).hom = 𝟙 (baseObj P) := sorry

/-- The first component of the forward identity comparison is the identity. -/
@[simp]
theorem mapId.component.hom.fst
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    fstMap (mapId.component F G P).hom = 𝟙 (fstObj P) := sorry

/-- The second component of the forward identity comparison is the identity. -/
@[simp]
theorem mapId.component.hom.snd
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    sndMap (mapId.component F G P).hom = 𝟙 (sndObj P) := sorry

/-- The base component of the inverse identity comparison is the identity. -/
@[simp]
theorem mapId.component.inv.base
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    baseMap (mapId.component F G P).inv = 𝟙 (baseObj P) := sorry

/-- The first component of the inverse identity comparison is the identity. -/
@[simp]
theorem mapId.component.inv.fst
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    fstMap (mapId.component F G P).inv = 𝟙 (fstObj P) := sorry

/-- The second component of the inverse identity comparison is the identity. -/
@[simp]
theorem mapId.component.inv.snd
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    sndMap (mapId.component F G P).inv = 𝟙 (sndObj P) := sorry

/-- The explicit identity-comparison components are natural in pseudo-pullback morphisms. -/
theorem mapId.component.naturality
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (map (BasedCospanTransform.id F G)).map φ ≫
        (mapId.component F G Q).hom =
      (mapId.component F G P).hom ≫ φ := sorry

/-- Every forward identity-comparison component is vertical over the identity of its common
base object. -/
theorem mapId.component.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      (mapId.component F G P).hom := sorry

/-- Every inverse identity-comparison component is vertical over the identity of its common
base object. -/
theorem mapId.component.inv.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      (mapId.component F G P).inv := sorry

/-- Canonical componentwise based isomorphism witnessing identity preservation by the explicit
pseudo-pullback action. -/
@[stacks 0040 "identity comparison for maps of explicit pseudo-pullbacks"]
noncomputable def map.idIso (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    map (BasedCospanTransform.id F G) ≅
        𝟙 (PseudoPullback F G) :=
  BasedNatIso.ofComponents
    (mapId.component F G)
    (fun φ ↦ mapId.component.naturality F G φ)
    (mapId.component.isHomLift F G)

/-- Every forward packaged identity-comparison component is vertical over the identity of the
common base object. -/
theorem map.idIso.hom.app.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      ((map.idIso F G).hom.toNatTrans.app P) := sorry

/-- Every inverse packaged identity-comparison component is vertical over the identity of the
common base object. -/
theorem map.idIso.inv.app.isHomLift
    (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      ((map.idIso F G).inv.toNatTrans.app P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
