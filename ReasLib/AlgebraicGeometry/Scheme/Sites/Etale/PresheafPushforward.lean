/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPullback

/-!
# Presheaf pushforward and sheafification along a scheme morphism

For `g : Y' ⟶ Y`, the abelian presheaf pushforward `g_*` is precomposition with
`smallEtalePullback g`. A downstairs map `α : G ⟶ g_* G'` factors uniquely through
sheafification as `α^# : G^# ⟶ g_* ((G')^#)`, and `α'` is the adjunct of `α^#`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Abelian presheaf pushforward along `g : Y' ⟶ Y` on small étale sites, sending `G'` to
the presheaf `V ↦ G'((smallEtalePullback g).obj V)`. -/
noncomputable abbrev presheafPushforwardAb {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (whiskeringLeft _ _ _).obj (smallEtalePullback g).op

/-- Evaluating abelian presheaf pushforward is precomposition with `(smallEtalePullback g).op`. -/
theorem presheafPushforwardAb_obj {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (presheafPushforwardAb g).obj G' = (smallEtalePullback g).op ⋙ G' :=
  rfl

/-- The value of `g_* G'` at an étale `V` over `Y` is `G'` at the base change of `V` along `g`. -/
theorem presheafPushforwardAb_app {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Y.Etale) :
    ((presheafPushforwardAb g).obj G').obj (op V) =
      G'.obj (op ((smallEtalePullback g).obj V)) :=
  rfl

/-- Sheaf-level abelian pushforward is the presheaf pushforward of the underlying presheaf. -/
theorem sheafToPresheaf_presheafPushforwardAb {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u}) :
    (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((smallEtalePushforwardAb g).obj F) =
      (presheafPushforwardAb g).obj F.obj :=
  rfl

/-- The unique sheaf map `α^# : G^# ⟶ g_* ((G')^#)` induced by a presheaf map
`α : G ⟶ g_* G'`, obtained by sheafifying through the unit of `G'`. -/
noncomputable def sheafifyPresheafPushforward {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G') :
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G ⟶
      (smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G') :=
  ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).homEquiv G
      ((smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G'))).symm
    (α ≫ whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G'))

/-- The underlying presheaf map of `α^#` is the sheafification lift of
`α ≫ g_* (toSheafify G')`. -/
theorem sheafifyPresheafPushforward_hom {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G') :
    (sheafifyPresheafPushforward g α).hom =
      sheafifyLift Y.smallEtaleTopology
        (α ≫ whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G'))
        ((smallEtalePushforwardAb g).obj
          ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G')).property :=
  rfl

/-- The sheafification-unit square for `α^#` commutes. -/
theorem sheafifyPresheafPushforward_commSq {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G') :
    CommSq α (toSheafify Y.smallEtaleTopology G)
      (whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G'))
      (sheafifyPresheafPushforward g α).hom := by
  refine ⟨?_⟩
  rw [sheafifyPresheafPushforward_hom]
  exact (toSheafify_sheafifyLift Y.smallEtaleTopology _ _).symm

/-- A sheaf map `G^# ⟶ g_* ((G')^#)` making the sheafification-unit square commute equals
`sheafifyPresheafPushforward`. -/
theorem sheafifyPresheafPushforward_unique {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (β : (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G ⟶
      (smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G'))
    (hβ : CommSq α (toSheafify Y.smallEtaleTopology G)
      (whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G')) β.hom) :
    β = sheafifyPresheafPushforward g α := by
  apply Sheaf.hom_ext
  rw [sheafifyPresheafPushforward_hom]
  exact sheafifyLift_unique Y.smallEtaleTopology _ _ β.hom hβ.w.symm

/-- The adjunct `α' : g⁻¹ G^# ⟶ (G')^#` of `α^#`. -/
noncomputable def sheafifyPresheafPushforwardAdjoint {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G') :
    ((smallEtalePullback g).sheafPullback AddCommGrpCat.{u}
          Y.smallEtaleTopology Y'.smallEtaleTopology).obj
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G) ⟶
      (presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G' :=
  let adj := (smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology Y'.smallEtaleTopology
  (adj.homEquiv
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)
      ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G')).symm
    (sheafifyPresheafPushforward g α)

/-- Applying the sheaf adjunction equivalence to `α'` recovers `α^#`. -/
theorem sheafifyPresheafPushforwardAdjoint_homEquiv {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G') :
    ((smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology Y'.smallEtaleTopology).homEquiv
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G')
        (sheafifyPresheafPushforwardAdjoint g α) =
      sheafifyPresheafPushforward g α := by
  unfold sheafifyPresheafPushforwardAdjoint
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Scheme.Etale
