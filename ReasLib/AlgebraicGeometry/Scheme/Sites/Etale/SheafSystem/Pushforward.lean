/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe uI u

namespace AlgebraicGeometry.Scheme.Etale.SheafSystem

variable {I : Type uI} [Preorder I]
variable {D : PreorderInverseSystem I Scheme.{u}}
variable {c : Cone D}

/-- Direct image of a sheaf on the limit along the stage projection `π_i`. -/
noncomputable abbrev stagePushforward
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    Sheaf (D.obj (op i)).smallEtaleTopology (Type (u + 1)) :=
  pushforwardAlong (c.π.app (op i)) F

/-- The adjunction mate associated to a transition of the inverse system. -/
noncomputable def stageTransition
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    (pullback D hij).obj (stagePushforward F i) ⟶ stagePushforward F j :=
  (((smallEtalePullback (D.transitionMap hij)).sheafAdjunctionContinuous (Type (u + 1))
        (D.obj (op i)).smallEtaleTopology (D.obj (op j)).smallEtaleTopology).homEquiv
      (stagePushforward F i) (stagePushforward F j)).symm
    (eqToHom (congrArg (fun t => pushforwardAlong t F) (c.w (homOfLE hij).op).symm) ≫
      (pushforwardCompIso (c.π.app (op j)) (D.transitionMap hij)).inv.app F)

/-- The transition maps of the stage pushforwards satisfy the pullback cocycle law. -/
theorem stageTransition_comp
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (pullbackCompIso D hij hjk).hom.app (stagePushforward F i) ≫
        stageTransition F (le_trans hij hjk) =
      (pullback D hjk).map (stageTransition F hij) ≫ stageTransition F hjk := sorry

/-- The inverse system of small-etale pushforwards of a sheaf along the limit projections. -/
noncomputable def pushforwardSystem
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) : SheafSystem D :=
  SheafSystem.of (stagePushforward F) (stageTransition F) (stageTransition_comp F)

/-- The stage sheaf of `pushforwardSystem` is the projection pushforward. -/
theorem pushforwardSystem_obj
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    (pushforwardSystem F).obj i = stagePushforward F i := rfl

/-- The transition of `pushforwardSystem` is the canonical adjunction mate. -/
theorem pushforwardSystem_transition
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    (pushforwardSystem F).transition hij = stageTransition F hij := rfl

/-- Inverse image of the stage pushforward along the same projection. -/
noncomputable abbrev stagePullbackPushforward
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    Sheaf c.pt.smallEtaleTopology (Type (u + 1)) :=
  pullbackAlong (c.π.app (op i)) (stagePushforward F i)

/-- The adjunction counit from the pulled-back stage pushforward to the original sheaf. -/
noncomputable abbrev stageCounit
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    stagePullbackPushforward F i ⟶ F :=
  counitAlong (c.π.app (op i)) F

/-- The structure map between pulled-back stage pushforwards. -/
noncomputable def colimitDiagramMap
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    stagePullbackPushforward F i ⟶ stagePullbackPushforward F j :=
  eqToHom (congrArg (fun t => pullbackAlong t (stagePushforward F i))
      (c.w (homOfLE hij).op).symm) ≫
    (pullbackSheafCompIso (c.π.app (op j)) (D.transitionMap hij)).hom.app
      (stagePushforward F i) ≫
    pullbackAlongMap (c.π.app (op j)) (stageTransition F hij)

/-- The identity law for the pulled-back stage transition maps. -/
theorem colimitDiagramMap_id
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    colimitDiagramMap F (le_refl i) = 𝟙 (stagePullbackPushforward F i) := sorry

/-- The composition law for the pulled-back stage transition maps. -/
theorem colimitDiagramMap_comp
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    colimitDiagramMap F (le_trans hij hjk) =
      colimitDiagramMap F hij ≫ colimitDiagramMap F hjk := sorry

/-- The directed diagram of pulled-back stage pushforwards on the limit scheme. -/
noncomputable def colimitDiagram
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    I ⥤ Sheaf c.pt.smallEtaleTopology (Type (u + 1)) where
  obj i := stagePullbackPushforward F i
  map {i j} hij := colimitDiagramMap F (leOfHom hij)
  map_id := fun i => colimitDiagramMap_id F i
  map_comp := fun hij hjk => colimitDiagramMap_comp F (leOfHom hij) (leOfHom hjk)

set_option backward.isDefEq.respectTransparency false in
private theorem counitAlong_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (hp : f ≫ g = p)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    eqToHom (congrArg (fun t => pullbackAlong t (pushforwardAlong p F)) hp.symm) ≫
        (pullbackSheafCompIso f g).hom.app (pushforwardAlong p F) ≫
        pullbackAlongMap f
          ((((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
              Z.smallEtaleTopology Y.smallEtaleTopology).homEquiv
            (pushforwardAlong p F) (pushforwardAlong f F)).symm
            (eqToHom (congrArg (fun t => pushforwardAlong t F) hp.symm) ≫
              (pushforwardCompIso f g).inv.app F)) ≫
        counitAlong f F = counitAlong p F := by
  subst p
  simp only [eqToHom_refl, Category.id_comp]
  let a₁ := (smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
    Z.smallEtaleTopology Y.smallEtaleTopology
  let a₂ := (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
    Y.smallEtaleTopology X.smallEtaleTopology
  let a₃ := (smallEtalePullback (f ≫ g)).sheafAdjunctionContinuous (Type (u + 1))
    Z.smallEtaleTopology X.smallEtaleTopology
  have h := conjugateEquiv_counit_symm a₃ (a₁.comp a₂) (pushforwardCompIso f g).inv F
  change _ = (Adjunction.leftAdjointCompIso a₁ a₂ a₃ (pushforwardCompIso f g)).hom.app
    (pushforwardAlong (f ≫ g) F) ≫ a₃.counit.app F at h
  change (Adjunction.leftAdjointCompIso a₁ a₂ a₃ (pushforwardCompIso f g)).inv.app
      (pushforwardAlong (f ≫ g) F) ≫
        ((smallEtalePullback f).sheafPullback (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology).map
            ((a₁.homEquiv _ _).symm ((pushforwardCompIso f g).inv.app F)) ≫
        a₂.counit.app F = a₃.counit.app F
  calc
    _ = (Adjunction.leftAdjointCompIso a₁ a₂ a₃ (pushforwardCompIso f g)).inv.app
        (pushforwardAlong (f ≫ g) F) ≫
          (((smallEtalePullback g).sheafPullback (Type (u + 1))
            Z.smallEtaleTopology Y.smallEtaleTopology ⋙
              (smallEtalePullback f).sheafPullback (Type (u + 1))
                Y.smallEtaleTopology X.smallEtaleTopology).map
                  ((pushforwardCompIso f g).inv.app F) ≫ (a₁.comp a₂).counit.app F) := by
      rw [Adjunction.homEquiv_counit, Functor.map_comp, Adjunction.comp_counit_app]
      dsimp only [Functor.comp_obj, Functor.id_obj]
      simp only [Functor.comp_map, Category.assoc]
    _ = (Adjunction.leftAdjointCompIso a₁ a₂ a₃ (pushforwardCompIso f g)).inv.app
        (pushforwardAlong (f ≫ g) F) ≫
          ((Adjunction.leftAdjointCompIso a₁ a₂ a₃ (pushforwardCompIso f g)).hom.app
            (pushforwardAlong (f ≫ g) F) ≫ a₃.counit.app F) := congrArg (fun t => _ ≫ t) h
    _ = a₃.counit.app F := by simp

/-- The counit legs form a cocone over the pulled-back stage pushforward diagram. -/
theorem stageCounit_naturality
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    colimitDiagramMap F hij ≫ stageCounit F j = stageCounit F i :=
  counitAlong_comp (c.π.app (op j)) (D.transitionMap hij) (c.π.app (op i))
    (c.w (homOfLE hij).op) F

/-- The cocone of stage counits with vertex the original sheaf. -/
noncomputable def counitCocone
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    Cocone (colimitDiagram F) where
  pt := F
  ι :=
    { app := fun i => stageCounit F i
      naturality := fun _ _ hij => stageCounit_naturality F (leOfHom hij) }

/-- The stage and transition components of the constructed pushforward system. -/
theorem pushforwardSystem_spec
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    (pushforwardSystem F).obj i = stagePushforward F i ∧
      (pushforwardSystem F).transition hij = stageTransition F hij :=
  ⟨pushforwardSystem_obj F i, pushforwardSystem_transition F hij⟩

/-- The explicit counit cocone is a colimit under the directed affine limit hypotheses. -/
theorem counitCocone_isColimit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.transitionMap hij)]
    (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    Nonempty (IsColimit (counitCocone F)) := sorry

variable [HasColimitsOfShape I (Sheaf c.pt.smallEtaleTopology (Type (u + 1)))]

/-- The comparison induced by the counit cocone and a chosen colimit. -/
noncomputable def comparison
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    colimit (colimitDiagram F) ⟶ F :=
  colimit.desc (colimitDiagram F) (counitCocone F)

/-- The comparison restricts to the counit on every stage. -/
theorem comparison_ι
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) (i : I) :
    colimit.ι (colimitDiagram F) i ≫ comparison F = stageCounit F i :=
  colimit.ι_desc (counitCocone F) i

/-- The chosen-colimit comparison is an isomorphism under the directed affine limit hypotheses. -/
theorem comparison_isIso [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.transitionMap hij)]
    (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    IsIso (comparison F) :=
  (colimit.isColimit (colimitDiagram F)).nonempty_isColimit_iff_isIso_desc.mp
    (counitCocone_isColimit hc F)

end AlgebraicGeometry.Scheme.Etale.SheafSystem

