module

public import Mathlib.CategoryTheory.GradedObject
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback-pushforward adjunction for graded modules on ringed sites

Module pullback and pushforward extend pointwise to graded objects.  This file owns the resulting
functors, their Hom equivalence, and the graded adjunction.  The grading type is arbitrary; the
integer-graded statement used in Chapter 24 is a specialization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

namespace Graded

/-- Degreewise direct image of graded module sheaves along a morphism of ringed sites. -/
@[stacks 0FR8 "graded module pushforward"]
abbrev pushforward.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) :
    GradedObject I (ModuleCat.{z} X) ⥤ GradedObject I (ModuleCat.{z} Y) :=
  Functor.pi (fun _ : I ↦ f.modulePushforward.{z})

/-- Evaluation of graded module pushforward on an object is degreewise module pushforward. -/
@[simp] theorem pushforward_obj_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) (A : GradedObject I (ModuleCat.{z} X)) (i : I) :
    ((pushforward f).obj A) i = f.modulePushforward.obj (A i) := sorry

/-- Evaluation of graded module pushforward on a morphism is degreewise module pushforward. -/
@[simp] theorem pushforward_map_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) {A A' : GradedObject I (ModuleCat.{z} X)} (g : A ⟶ A') (i : I) :
    ((pushforward f).map g) i = f.modulePushforward.map (g i) := sorry

/-- Degreewise inverse image of graded module sheaves along a morphism of ringed sites. -/
@[stacks 0FR8 "graded module pullback"]
abbrev pullback.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    GradedObject I (ModuleCat.{z} Y) ⥤ GradedObject I (ModuleCat.{z} X) :=
  Functor.pi (fun _ : I ↦ f.modulePullback.{z})

/-- Evaluation of graded module pullback on an object is degreewise module pullback. -/
@[simp] theorem pullback_obj_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (i : I) :
    ((pullback f).obj B) i = f.modulePullback.obj (B i) := sorry

/-- Evaluation of graded module pullback on a morphism is degreewise module pullback. -/
@[simp] theorem pullback_map_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    {B B' : GradedObject I (ModuleCat.{z} Y)} (g : B ⟶ B') (i : I) :
    ((pullback f).map g) i = f.modulePullback.map (g i) := sorry

/-- The Hom equivalence obtained by applying the module pullback-pushforward adjunction in every
degree. -/
@[stacks 0FR8 "graded module pullback-pushforward Hom equivalence"]
noncomputable def homEquiv.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X)) :
    ((pullback f).obj B ⟶ A) ≃ (B ⟶ (pushforward f).obj A) :=
  Equiv.piCongrRight (fun i ↦ f.modulePullbackHomEquiv (B i) (A i))

/-- The graded Hom equivalence acts in each degree by the module Hom equivalence. -/
@[simp] theorem homEquiv_apply_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X))
    (g : (pullback f).obj B ⟶ A) (i : I) :
    (homEquiv f B A g) i = f.modulePullbackHomEquiv (B i) (A i) (g i) := sorry

/-- The inverse graded Hom equivalence acts in each degree by the inverse module Hom
equivalence. -/
@[simp] theorem homEquiv_symm_apply_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X))
    (g : B ⟶ (pushforward f).obj A) (i : I) :
    ((homEquiv f B A).symm g) i =
      (f.modulePullbackHomEquiv (B i) (A i)).symm (g i) := sorry

/-- Naturality of the inverse graded Hom equivalence in the graded module on the target. -/
theorem homEquiv_naturality_left_symm.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    {B' B : GradedObject I (ModuleCat.{z} Y)} {A : GradedObject I (ModuleCat.{z} X)}
    (g : B' ⟶ B) (h : B ⟶ (pushforward f).obj A) :
    (homEquiv f B' A).symm (g ≫ h) =
      (pullback f).map g ≫ (homEquiv f B A).symm h := sorry

/-- Naturality of the graded Hom equivalence in the graded module on the source. -/
theorem homEquiv_naturality_right.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    {B : GradedObject I (ModuleCat.{z} Y)} {A A' : GradedObject I (ModuleCat.{z} X)}
    (g : (pullback f).obj B ⟶ A) (h : A ⟶ A') :
    homEquiv f B A' (g ≫ h) =
      homEquiv f B A g ≫ (pushforward f).map h := sorry

/-- Lemma 24.9.1 (0FR8): degreewise module pullback is left adjoint to degreewise module
pushforward on graded objects. -/
@[stacks 0FR8 "graded module pullback-pushforward adjunction"]
noncomputable def adjunction.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    pullback (I := I) f ⊣ pushforward (I := I) f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv f
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm f
      homEquiv_naturality_right := homEquiv_naturality_right f }

/-- Degreewise graded module pullback is recognized as a left adjoint. -/
instance pullbackIsLeftAdjoint.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    (pullback (I := I) f).IsLeftAdjoint :=
  (adjunction (I := I) f).isLeftAdjoint

/-- Degreewise graded module pushforward is recognized as a right adjoint. -/
instance pushforwardIsRightAdjoint.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    (pushforward.{uI, z} (I := I) f).IsRightAdjoint :=
  (adjunction (I := I) f).isRightAdjoint

/-- The Hom equivalence of the graded adjunction is the pointwise graded Hom equivalence. -/
@[simp] theorem adjunction_homEquiv.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X)) :
    (adjunction (I := I) f).homEquiv B A = homEquiv f B A := sorry

end Graded

/-! Compatibility names for the Chapter 24 graded-module API. -/

/-- Compatibility name for degreewise direct image of graded module sheaves. -/
abbrev gradedPushforward.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) :
    GradedObject I (ModuleCat.{z} X) ⥤ GradedObject I (ModuleCat.{z} Y) :=
  Graded.pushforward f

/-- Compatibility name for degreewise inverse image of graded module sheaves. -/
abbrev gradedPullback.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    GradedObject I (ModuleCat.{z} Y) ⥤ GradedObject I (ModuleCat.{z} X) :=
  Graded.pullback f

/-- Compatibility orientation of the graded pullback-pushforward Hom equivalence. -/
noncomputable abbrev gradedPushforwardPullbackHomEquiv.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X)) :
    (B ⟶ (gradedPushforward f).obj A) ≃ ((gradedPullback f).obj B ⟶ A) :=
  (Graded.homEquiv f B A).symm

/-- Compatibility evaluation formula for the inverse source-oriented graded Hom equivalence. -/
@[simp] theorem gradedPushforwardPullbackHomEquiv_symm_apply_apply.{uI, z, uX, vX, uY, vY, w}
    {I : Type uI} {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (B : GradedObject I (ModuleCat.{z} Y)) (A : GradedObject I (ModuleCat.{z} X))
    (g : (gradedPullback f).obj B ⟶ A) (i : I) :
    ((gradedPushforwardPullbackHomEquiv f B A).symm g) i =
      f.modulePullbackHomEquiv (B i) (A i) (g i) := sorry

end RingedSite.Hom
