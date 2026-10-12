/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    (pushforwardSystem F).obj i = stagePushforward F i := sorry

/-- The transition of `pushforwardSystem` is the canonical adjunction mate. -/
theorem pushforwardSystem_transition
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    (pushforwardSystem F).transition hij = stageTransition F hij := sorry

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

/-- The counit legs form a cocone over the pulled-back stage pushforward diagram. -/
theorem stageCounit_naturality
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) {i j : I} (hij : i ≤ j) :
    colimitDiagramMap F hij ≫ stageCounit F j = stageCounit F i := sorry

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
      (pushforwardSystem F).transition hij = stageTransition F hij := sorry

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
    colimit.ι (colimitDiagram F) i ≫ comparison F = stageCounit F i := sorry

/-- The chosen-colimit comparison is an isomorphism under the directed affine limit hypotheses. -/
theorem comparison_isIso [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.transitionMap hij)]
    (hc : IsLimit c)
    (F : Sheaf c.pt.smallEtaleTopology (Type (u + 1))) :
    IsIso (comparison F) := sorry

end AlgebraicGeometry.Scheme.Etale.SheafSystem

