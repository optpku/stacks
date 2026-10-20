/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localized slice sites from selected covers

A localized slice is controlled by a selected precoverage, rather than by all
covers in its generated Grothendieck topology.  This distinction retains the
chosen geometric class of arrows, such as etale arrows.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Precoverage.LocalizedSlice

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

/-- A family of full localized slices closed under selected covers and base change. -/
@[stacks 0GWL]
class Family (K : Precoverage C) (τ : ∀ U : C, ObjectProperty (Over U)) : Prop where
  /-- The identity arrow belongs to each localized slice. -/
  id_mem (U : C) : τ U (Over.mk (𝟙 U))
  /-- A member of a selected cover of a localized object remains localized after
  composition with its structural arrow. -/
  cover_mem {U : C} {X : Over U} (hX : τ U X) {R : Presieve X.left}
      (hR : R ∈ K X.left) {Y : C} (g : Y ⟶ X.left) (hg : R g) :
      τ U (Over.mk (g ≫ X.hom))
  /-- Localized objects remain localized after base change. -/
  pullback_mem {U V : C} (f : V ⟶ U) {X : Over U} (hX : τ U X) :
      τ V ((Over.pullback f).obj X)

/-- Every arrow in a selected cover is an object of the corresponding localized
slice. -/
theorem cover_mem (K : Precoverage C) (τ : ∀ U : C, ObjectProperty (Over U))
    [Family K τ] {U V : C} {R : Presieve U}
    (hR : R ∈ K U) (f : V ⟶ U) (hf : R f) : τ U (Over.mk f) := sorry

/-- Base change between the full subcategories defining two localized slices. -/
noncomputable def baseChange (K : Precoverage C)
    (τ : ∀ U : C, ObjectProperty (Over U)) [Family K τ] {U V : C} (f : V ⟶ U) :
    (τ U).FullSubcategory ⥤ (τ V).FullSubcategory where
  obj X := ⟨(Over.pullback f).obj X.obj, Family.pullback_mem (K := K) (τ := τ) f X.property⟩
  map h := ObjectProperty.homMk ((Over.pullback f).map h.hom)
  map_id := sorry
  map_comp := sorry

/-- The topology on a localized slice induced from the ambient slice topology. -/
abbrev topology (J : GrothendieckTopology C) (τ : ∀ U : C, ObjectProperty (Over U))
    (U : C) : GrothendieckTopology ((τ U).FullSubcategory) :=
  ((τ U).ι).inducedTopology (J.over U)

/-- Type-valued sheaves on a localized slice. -/
abbrev Sheaf (J : GrothendieckTopology C) (τ : ∀ U : C, ObjectProperty (Over U))
    (U : C) :=
  _root_.CategoryTheory.Sheaf (topology J τ U) (Type (max u v))

/-- Chosen inverse-image functors between localized slice sites. The data is explicit because
base change need not induce a canonical sheaf pullback without additional geometric hypotheses. -/
@[stacks 0GWL]
structure InverseImage (K : Precoverage C) (J : GrothendieckTopology C)
    (τ : ∀ U : C, ObjectProperty (Over U)) [Family K τ] where
  /-- The inverse image attached to an arrow of the ambient category. -/
  pullback {U V : C} (f : V ⟶ U) : Sheaf J τ U ⥤ Sheaf J τ V
  /-- Inverse image along an identity is canonically the identity. -/
  pullbackId (U : C) : pullback (𝟙 U) ≅ 𝟭 (Sheaf J τ U)
  /-- Inverse image along a composite agrees with the composite inverse image. -/
  pullbackComp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f)

namespace InverseImage

/-- The comparison between iterated and composite inverse image, evaluated at a sheaf. -/
def pullbackCompObj {K : Precoverage C} {J : GrothendieckTopology C}
    {τ : ∀ U : C, ObjectProperty (Over U)} [Family K τ]
    (ι : InverseImage K J τ) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (F : Sheaf J τ U) :
    (ι.pullback g).obj ((ι.pullback f).obj F) ≅ (ι.pullback (g ≫ f)).obj F :=
  (ι.pullbackComp f g).app F

end InverseImage

/-- Compatible sheaves on localized slices, with transition maps invertible exactly along the
selected local arrows. -/
@[stacks 0GWL]
structure Glueing (K : Precoverage C) (J : GrothendieckTopology C)
    (τ : ∀ U : C, ObjectProperty (Over U)) [Family K τ]
    (ι : InverseImage K J τ) where
  /-- The localized sheaf over each ambient object. -/
  obj (U : C) : Sheaf J τ U
  /-- The transition morphism along an ambient arrow. -/
  transition {U V : C} (f : V ⟶ U) : (ι.pullback f).obj (obj U) ⟶ obj V
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (U : C) : transition (𝟙 U) = (ι.pullbackId U).hom.app (obj U)
  /-- Transition morphisms satisfy the base-change cocycle condition. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    CommSq ((ι.pullbackComp f g).hom.app (obj U)) ((ι.pullback g).map (transition f))
      (transition (g ≫ f)) (transition g)
  /-- Transitions along locally selected arrows are invertible. -/
  isIso_transition_of_mem {U V : C} (f : V ⟶ U) (hf : τ U (Over.mk f)) :
    IsIso (transition f)

namespace Glueing

/-- The two-step transition morphism obtained by pulling back the first transition and then
applying the second. -/
def composedTransition {K : Precoverage C} {J : GrothendieckTopology C}
    {τ : ∀ U : C, ObjectProperty (Over U)} [Family K τ]
    {ι : InverseImage K J τ} (F : Glueing K J τ ι)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (ι.pullback g).obj ((ι.pullback f).obj (F.obj U)) ⟶ F.obj W :=
  (ι.pullback g).map (F.transition f) ≫ F.transition g

/-- A compatible family has identity transitions, cocycle-compatible transitions, and
invertible transitions along selected local arrows. -/
theorem spec {K : Precoverage C} {J : GrothendieckTopology C}
    {τ : ∀ U : C, ObjectProperty (Over U)} [Family K τ]
    {ι : InverseImage K J τ} (F : Glueing K J τ ι) :
    (∀ U : C, F.transition (𝟙 U) = (ι.pullbackId U).hom.app (F.obj U)) ∧
      (∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
        CommSq ((ι.pullbackComp f g).hom.app (F.obj U))
          ((ι.pullback g).map (F.transition f)) (F.transition (g ≫ f)) (F.transition g)) ∧
      (∀ {U V : C} (f : V ⟶ U) (hf : τ U (Over.mk f)), IsIso (F.transition f)) := sorry

end Glueing

end CategoryTheory.Precoverage.LocalizedSlice
