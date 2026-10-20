/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.ObjectComputations
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.MorphismComputations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection comparisons for explicit pseudo-pullback maps

This leaf owns the first- and second-projection comparison isomorphisms of the explicit map of
based pseudo-pullbacks, together with their objectwise, naturality, and verticality formulas.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- Projecting an explicit pseudo-pullback map to the left recovers the left component of the
cospan transformation. -/
theorem map.fstCommutes
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map ψ ⋙ fst F₂ G₂ = fst F₁ G₁ ⋙ ψ.left := sorry
/- Proof strategy: ext on underlying functors, then on pseudo-pullback morphisms. Both sides are
exactly the left object and map components chosen in `mapObj` and `mapMap`. -/

/-- Projecting an explicit pseudo-pullback map to the right recovers the right component of the
cospan transformation. -/
theorem map.sndCommutes
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map ψ ⋙ snd F₂ G₂ = snd F₁ G₁ ⋙ ψ.right := sorry
/- Proof strategy: the symmetric argument to `map.fstCommutes`; functor extensionality reduces the claim
to the right components stored by `mapObj` and `mapMap`. -/

/-- The objectwise first-projection comparison for an induced pseudo-pullback map. Both sides
have the same explicit first component, so the comparison is the identity isomorphism. -/
def map.fstComponent
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map ψ ⋙ fst F₂ G₂).obj P ≅ (fst F₁ G₁ ⋙ ψ.left).obj P :=
  Iso.refl _

/-- The objectwise first-projection comparisons are natural in pseudo-pullback morphisms. -/
theorem map.fstComponent.naturality
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    (map ψ ⋙ fst F₂ G₂).map φ ≫ (map.fstComponent ψ Q).hom =
      (map.fstComponent ψ P).hom ≫ (fst F₁ G₁ ⋙ ψ.left).map φ := sorry

/-- The inverse first-projection comparison is natural in the reverse orientation. -/
@[reassoc]
theorem map.fstComponent.invNaturality
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    (map.fstComponent ψ P).inv ≫ (map ψ ⋙ fst F₂ G₂).map φ =
      (fst F₁ G₁ ⋙ ψ.left).map φ ≫ (map.fstComponent ψ Q).inv := sorry

/-- Every forward first-projection comparison component is vertical over the identity common
base map. -/
theorem map.fstComponent.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₂.p.IsHomLift (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (map.fstComponent ψ P).hom := sorry

/-- Every inverse first-projection comparison component is vertical over the identity common
base map. -/
theorem map.fstComponent.inv.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₂.p.IsHomLift (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (map.fstComponent ψ P).inv := sorry

/-- Componentwise isomorphism by which an induced pseudo-pullback map commutes with the first
projection. Its non-`Prop` components are identities. -/
@[stacks 0040 "first projection comparison for a map of explicit pseudo-pullbacks"]
def map.fstIso
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map ψ ⋙ fst F₂ G₂ ≅ fst F₁ G₁ ⋙ ψ.left :=
  BasedNatIso.ofComponents
    (map.fstComponent ψ)
    (fun φ ↦ map.fstComponent.naturality ψ φ)
    (map.fstComponent.isHomLift ψ)

/-- The forward component of the first-projection comparison is the identity. -/
@[simp] theorem map.fstIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.fstIso ψ).hom.toNatTrans.app P =
      (map.fstComponent ψ P).hom := sorry

/-- The inverse component of the first-projection comparison is the identity. -/
@[simp] theorem map.fstIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.fstIso ψ).inv.toNatTrans.app P =
      (map.fstComponent ψ P).inv := sorry

/-- Every forward component of the packaged first-projection comparison is vertical over the
identity common base map. -/
theorem map.fstIso.hom.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₂.p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.fstIso ψ).hom.toNatTrans.app P) := sorry

/-- Every inverse component of the packaged first-projection comparison is vertical over the
identity common base map. -/
theorem map.fstIso.inv.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₂.p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.fstIso ψ).inv.toNatTrans.app P) := sorry

/-- The objectwise second-projection comparison for an induced pseudo-pullback map. Both sides
have the same explicit second component, so the comparison is the identity isomorphism. -/
def map.sndComponent
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map ψ ⋙ snd F₂ G₂).obj P ≅ (snd F₁ G₁ ⋙ ψ.right).obj P :=
  Iso.refl _

/-- The objectwise second-projection comparisons are natural in pseudo-pullback morphisms. -/
theorem map.sndComponent.naturality
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    (map ψ ⋙ snd F₂ G₂).map φ ≫ (map.sndComponent ψ Q).hom =
      (map.sndComponent ψ P).hom ≫ (snd F₁ G₁ ⋙ ψ.right).map φ := sorry

/-- The inverse second-projection comparison is natural in the reverse orientation. -/
@[reassoc]
theorem map.sndComponent.invNaturality
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    {P Q : (PseudoPullback F₁ G₁).obj} (φ : P ⟶ Q) :
    (map.sndComponent ψ P).inv ≫ (map ψ ⋙ snd F₂ G₂).map φ =
      (snd F₁ G₁ ⋙ ψ.right).map φ ≫ (map.sndComponent ψ Q).inv := sorry

/-- Every forward second-projection comparison component is vertical over the identity common
base map. -/
theorem map.sndComponent.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₂.p.IsHomLift (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (map.sndComponent ψ P).hom := sorry

/-- Every inverse second-projection comparison component is vertical over the identity common
base map. -/
theorem map.sndComponent.inv.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₂.p.IsHomLift (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      (map.sndComponent ψ P).inv := sorry

/-- Componentwise isomorphism by which an induced pseudo-pullback map commutes with the second
projection. Its non-`Prop` components are identities. -/
@[stacks 0040 "second projection comparison for a map of explicit pseudo-pullbacks"]
def map.sndIso
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map ψ ⋙ snd F₂ G₂ ≅ snd F₁ G₁ ⋙ ψ.right :=
  BasedNatIso.ofComponents
    (map.sndComponent ψ)
    (fun φ ↦ map.sndComponent.naturality ψ φ)
    (map.sndComponent.isHomLift ψ)

/-- The forward component of the second-projection comparison is the identity. -/
@[simp] theorem map.sndIso.hom.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.sndIso ψ).hom.toNatTrans.app P =
      (map.sndComponent ψ P).hom := sorry

/-- The inverse component of the second-projection comparison is the identity. -/
@[simp] theorem map.sndIso.inv.app
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map.sndIso ψ).inv.toNatTrans.app P =
      (map.sndComponent ψ P).inv := sorry

/-- Every forward component of the packaged second-projection comparison is vertical over the
identity common base map. -/
theorem map.sndIso.hom.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₂.p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.sndIso ψ).hom.toNatTrans.app P) := sorry

/-- Every inverse component of the packaged second-projection comparison is vertical over the
identity common base map. -/
theorem map.sndIso.inv.app.isHomLift
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₂.p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P))
      ((map.sndIso ψ).inv.toNatTrans.app P) := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
