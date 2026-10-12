/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition coherence for explicit pseudo-pullback maps

This leaf owns the objectwise and based natural isomorphisms comparing the pseudo-pullback map of
a composite cospan transformation with the composite of the two induced maps.
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
universe uX₃ vX₃ uY₃ vY₃ uS₃ vS₃

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
variable {X₃ : BasedCategory.{vX₃, uX₃} C}
variable {Y₃ : BasedCategory.{vY₃, uY₃} C}
variable {S₃ : BasedCategory.{vS₃, uS₃} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}
variable {F₃ : X₃ ⥤ᵇ S₃} {G₃ : Y₃ ⥤ᵇ S₃}

/-- The identity component maps respect the two differently parenthesized comparison pastings
associated to a composite of cospan transformations. -/
theorem mapComp.component.comm
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    CommSq
      (F₃.toFunctor.map
        (𝟙 (fstObj (((map ψ) ⋙ map φ).obj P))))
      (comparison ((map (ψ.comp φ)).obj P))
      (comparison (((map ψ) ⋙ map φ).obj P))
      (G₃.toFunctor.map
        (𝟙 (sndObj (((map ψ) ⋙ map φ).obj P)))) := sorry

/-- The identity first-component map for composition coherence lies over the identity
common-base map. -/
theorem mapComp.component.fst.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₃.p.IsHomLift
      (𝟙 (baseObj (((map ψ) ⋙ map φ).obj P)))
      (𝟙 (fstObj (((map ψ) ⋙ map φ).obj P))) := sorry

/-- The identity second-component map for composition coherence lies over the identity
common-base map. -/
theorem mapComp.component.snd.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₃.p.IsHomLift
      (𝟙 (baseObj (((map ψ) ⋙ map φ).obj P)))
      (𝟙 (sndObj (((map ψ) ⋙ map φ).obj P))) := sorry

/-- The objectwise composition-comparison isomorphism for the explicit pseudo-pullback action.
Its base and endpoint maps are identities between the two canonical comparison pastings. -/
noncomputable def mapComp.component
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map (ψ.comp φ)).obj P ≅ ((map ψ) ⋙ map φ).obj P :=
  mkIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hom_fst := mapComp.component.fst.isHomLift ψ φ P)
    (hom_snd := mapComp.component.snd.isHomLift ψ φ P)
    (mapComp.component.comm ψ φ P)

/-- The base component of the forward composition comparison is the identity. -/
@[simp]
theorem mapComp.component.hom.base
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    baseMap (mapComp.component ψ φ P).hom =
      𝟙 (baseObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The first component of the forward composition comparison is the identity. -/
@[simp]
theorem mapComp.component.hom.fst
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    fstMap (mapComp.component ψ φ P).hom =
      𝟙 (fstObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The second component of the forward composition comparison is the identity. -/
@[simp]
theorem mapComp.component.hom.snd
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    sndMap (mapComp.component ψ φ P).hom =
      𝟙 (sndObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The base component of the inverse composition comparison is the identity. -/
@[simp]
theorem mapComp.component.inv.base
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    baseMap (mapComp.component ψ φ P).inv =
      𝟙 (baseObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The first component of the inverse composition comparison is the identity. -/
@[simp]
theorem mapComp.component.inv.fst
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    fstMap (mapComp.component ψ φ P).inv =
      𝟙 (fstObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The second component of the inverse composition comparison is the identity. -/
@[simp]
theorem mapComp.component.inv.snd
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    sndMap (mapComp.component ψ φ P).inv =
      𝟙 (sndObj (((map ψ) ⋙ map φ).obj P)) := sorry

/-- The explicit composition-comparison components are natural in pseudo-pullback morphisms. -/
theorem mapComp.component.naturality
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    {P Q : (PseudoPullback F₁ G₁).obj} (χ : P ⟶ Q) :
    (map (ψ.comp φ)).map χ ≫ (mapComp.component ψ φ Q).hom =
      (mapComp.component ψ φ P).hom ≫ ((map ψ) ⋙ map φ).map χ := sorry

/-- Every forward composition-comparison component is vertical over the identity of its common
base object. -/
theorem mapComp.component.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback F₃ G₃).p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (mapComp.component ψ φ P).hom := sorry

/-- Every inverse composition-comparison component is vertical over the identity of its common
base object. -/
theorem mapComp.component.inv.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback F₃ G₃).p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (mapComp.component ψ φ P).inv := sorry

/-- Canonical componentwise based isomorphism witnessing composition preservation by the
explicit pseudo-pullback action. -/
@[stacks 0040 "composition comparison for maps of explicit pseudo-pullbacks"]
noncomputable def map.compIso
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) ≅ map ψ ⋙ map φ :=
  BasedNatIso.ofComponents
    (mapComp.component ψ φ)
    (fun χ ↦ mapComp.component.naturality ψ φ χ)
    (mapComp.component.isHomLift ψ φ)

/-- Every forward packaged composition-comparison component is vertical over the identity of its
common base object. -/
theorem map.compIso.hom.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback F₃ G₃).p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.compIso ψ φ).hom.toNatTrans.app P) := sorry

/-- Every inverse packaged composition-comparison component is vertical over the identity of the
common base object. -/
theorem map.compIso.inv.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback F₃ G₃).p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.compIso ψ φ).inv.toNatTrans.app P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
