/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange.System
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.BaseChange
import StacksCheckRecall

@[expose] public section

/-! Remark 18.34.7 (09CX), sites-modules.tex:
a square of sheaves of rings and a compatible module morphism induce a
morphism of the inverse systems of principal parts. Its maps commute with
order transitions and composition, and induce a compatible morphism of the
first principal-parts short exact sequences. -/

open CategoryTheory SheafOfModules.RingedSite

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable (sq : CommSq a phi phi' b)
variable {F : ringedSiteModuleCategory J O₂}
variable {F' : ringedSiteModuleCategory J O₂'}
variable (alpha : F ⟶ (restrictionAlong b).obj F')

/- Remark 18.34.7 (1): A ring-sheaf square and a compatible module map induce
a morphism of the inverse systems of principal parts. -/
@[stacks 09CX] #check
  (SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap sq alpha :
    PrincipalParts.system phi F ⟶ PrincipalParts.system phi' F' ⋙ restrictionAlong b)

variable {k l : ℕᵒᵖ} (f : k ⟶ l)

/- Remark 18.34.7 (2): The induced maps commute with order transitions. -/
@[stacks 09CX] #check
  (SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap_naturality sq alpha f :
    (PrincipalParts.system phi F).map f ≫
        SheafOfModules.RingedSite.PrincipalParts.BaseChange.map sq alpha l.unop =
      SheafOfModules.RingedSite.PrincipalParts.BaseChange.map sq alpha k.unop ≫
        (PrincipalParts.system phi' F' ⋙ restrictionAlong b).map f)

variable {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
variable {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
variable (sq' : CommSq a' phi' phi'' b')
variable {F'' : ringedSiteModuleCategory J O₂''}
variable (alpha' : F' ⟶ (restrictionAlong b').obj F'')

/- Remark 18.34.7 (3): The induced system maps are compatible with composition. -/
@[stacks 09CX] #check
  (SheafOfModules.RingedSite.PrincipalParts.BaseChange.systemMap_comp sq alpha sq' alpha' :
    PrincipalParts.BaseChange.systemMap (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') =
      PrincipalParts.BaseChange.systemMap sq alpha ≫
        Functor.whiskerRight (PrincipalParts.BaseChange.systemMap sq' alpha') (restrictionAlong b))

variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/- Remark 18.34.7 (4): The induced maps give a morphism of the first
principal-parts short exact sequences. -/
@[stacks 09CX] #check
  (SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceMap sq alpha :
    SheafOfModules.RingedSite.PrincipalParts.FirstOrder.sequence phi F ⟶
      (SheafOfModules.RingedSite.PrincipalParts.FirstOrder.sequence phi' F').map (restrictionAlong b))

/- Remark 18.34.7 (5): The first-order sequence maps are compatible with composition. -/
@[stacks 09CX] #check
  (SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange.sequenceMap_comp sq sq' alpha alpha' :
    PrincipalParts.FirstOrder.BaseChange.sequenceMap (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') =
      PrincipalParts.FirstOrder.BaseChange.sequenceMap sq alpha ≫
        (restrictionAlong b).mapShortComplex.map
          (PrincipalParts.FirstOrder.BaseChange.sequenceMap sq' alpha'))
