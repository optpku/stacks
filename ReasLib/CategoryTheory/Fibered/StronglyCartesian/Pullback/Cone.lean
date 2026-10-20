/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Basic

/-!
# Canonical lifted pullback cone

This file packages the chosen strongly-cartesian pullback square as a cone and exposes its
limiting lift, projection, and extensionality API.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsStronglyCartesian.Pullback

open IsStronglyCartesian IsHomLift IsPreFibered

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ C) {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)

/-- The canonical total-category pullback cone obtained by lifting the second projection of the
chosen base pullback and then using the strongly cartesian universal property for the first
projection. Its point and second leg remain mathlib's chosen prefibered data. -/
noncomputable def cone
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    PullbackCone φ ψ :=
  PullbackCone.mk (fst p φ ψ)
    (IsPreFibered.pullbackMap (p := p) rfl
      (pullback.snd (p.map φ) (p.map ψ)))
    (fst_comp p φ ψ)

namespace cone

/-- The point of the canonical lifted pullback cone is mathlib's chosen pullback object over the
second projection of the base pullback. -/
@[simp]
theorem pt
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    (Pullback.cone p φ ψ).pt =
      IsPreFibered.pullbackObj (p := p) rfl
        (pullback.snd (p.map φ) (p.map ψ)) := sorry

/-- The first leg of the canonical lifted pullback cone is the named strongly cartesian first
projection. -/
@[simp]
theorem fst
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    (Pullback.cone p φ ψ).fst = Pullback.fst p φ ψ := sorry

/-- The second leg of the canonical lifted pullback cone is mathlib's chosen cartesian lift of the
second projection of the base pullback. -/
@[simp]
theorem snd
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    (Pullback.cone p φ ψ).snd =
      IsPreFibered.pullbackMap (p := p) rfl
        (pullback.snd (p.map φ) (p.map ψ)) := sorry

/-- The first leg of the canonical lifted pullback cone lifts the first projection of the chosen
base pullback. -/
theorem fst.isHomLift
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    p.IsHomLift (pullback.fst (p.map φ) (p.map ψ))
      (Pullback.cone p φ ψ).fst := sorry

/-- The second leg of the canonical lifted pullback cone lifts the second projection of the chosen
base pullback. -/
theorem snd.isHomLift
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    p.IsHomLift (pullback.snd (p.map φ) (p.map ψ))
      (Pullback.cone p φ ψ).snd := sorry

/-- The point of the canonical lifted pullback cone lies over the chosen pullback object in the
base category. -/
@[simp]
theorem obj_pt
    [p.IsPreFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    p.obj (Pullback.cone p φ ψ).pt = pullback (p.map φ) (p.map ψ) := sorry

/-- The canonical lift into the lifted pullback cone, expressed through the already established
pullback square. -/
private noncomputable def limitLift
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) : s.pt ⟶ (Pullback.cone p φ ψ).pt :=
  (Pullback.isPullback p φ ψ).lift s.fst s.snd s.condition

/-- The canonical lift has the prescribed first projection. -/
private theorem limitLiftFst
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) :
    limitLift p φ ψ s ≫ (Pullback.cone p φ ψ).fst = s.fst := sorry

/-- The canonical lift has the prescribed second projection. -/
private theorem limitLiftSnd
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) :
    limitLift p φ ψ s ≫ (Pullback.cone p φ ψ).snd = s.snd := sorry

/-- Every morphism of cones into the canonical lifted pullback cone is its canonical lift. -/
private theorem limitLiftUniq
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) (m : s.pt ⟶ (Pullback.cone p φ ψ).pt)
    (h : ∀ j, m ≫ (Pullback.cone p φ ψ).π.app j = s.π.app j) :
    m = limitLift p φ ψ s := sorry

/-- The canonical lifted pullback cone is limiting. Its lift operation is inherited from the
canonical `IsPullback` square, while the cone itself retains the explicit chosen point and legs. -/
noncomputable def isLimit
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ] :
    IsLimit (Pullback.cone p φ ψ) :=
  PullbackCone.isLimitAux (Pullback.cone p φ ψ) (limitLift p φ ψ)
    (limitLiftFst p φ ψ) (limitLiftSnd p φ ψ) (limitLiftUniq p φ ψ)

/-- The limiting cone's lift is the universal lift of the canonical pullback square. -/
@[simp]
theorem isLimit.lift
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) :
    (Pullback.cone.isLimit p φ ψ).lift s =
      (Pullback.isPullback p φ ψ).lift s.fst s.snd s.condition := sorry

/-- The limiting lift has the prescribed first projection. -/
@[reassoc (attr := simp)]
theorem isLimit.lift_fst
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) :
    (Pullback.cone.isLimit p φ ψ).lift s ≫ (Pullback.cone p φ ψ).fst =
      s.fst := sorry

/-- The limiting lift has the prescribed second projection. -/
@[reassoc (attr := simp)]
theorem isLimit.lift_snd
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    (s : PullbackCone φ ψ) :
    (Pullback.cone.isLimit p φ ψ).lift s ≫ (Pullback.cone p φ ψ).snd =
      s.snd := sorry

/-- Two morphisms into the canonical lifted pullback cone are equal when their composites with
both projections agree. -/
theorem isLimit.hom_ext
    [p.IsFibered] [HasPullback (p.map φ) (p.map ψ)]
    [p.IsStronglyCartesian (p.map φ) φ]
    {W : E} {f g : W ⟶ (Pullback.cone p φ ψ).pt}
    (hfst : f ≫ (Pullback.cone p φ ψ).fst = g ≫ (Pullback.cone p φ ψ).fst)
    (hsnd : f ≫ (Pullback.cone p φ ψ).snd = g ≫ (Pullback.cone p φ ψ).snd) :
    f = g := sorry

end cone
end CategoryTheory.Functor.IsStronglyCartesian.Pullback
