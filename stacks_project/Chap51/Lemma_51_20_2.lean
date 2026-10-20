/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Uniformity
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.ExtClass

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ProjectiveResolution

open Abelian

variable {R : Type u} [CommRing R]
variable {M M' : ModuleCat.{u} R} (α : M ⟶ M')
variable (P : ProjectiveResolution M) (P' : ProjectiveResolution M') (e : ℕ)

-- Local instance justification (search instability): elaborating the repeated Ext conditions times out before finding mathlib's canonical small ModuleCat Ext instance.
local instance sourceModuleCatHasExt : HasExt.{u} (ModuleCat.{u} R) :=
  instHasExtModuleCatOfSmall R

/- Lemma 51.20.2 -/
@[stacks 0G9V] #check
  (CategoryTheory.ProjectiveResolution.liftExtTor_tfae_of_isMPseudoCoherent α P P' e :
    CategoryTheory.ModuleCat.IsMPseudoCoherent M (-((e : ℤ)) - 1) →
      let c₁ := ∃ a : P.Hom P' α, ∀ i : ℕ, e < i → a.hom.f i = 0
      let c₂ := ∃ a : P.Hom P' α, a.hom.f (e + 1) = 0
      let c₃ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
        (Ext.mk₀.{u} α).precomp N (zero_add i) = 0
      let c₄ := ∀ N : ModuleCat.{u} R,
        (Ext.mk₀.{u} α).precomp N (zero_add (e + 1)) = 0
      let c₅ := (Ext.mk₀.{u} α).comp
        (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0
      let c₆ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
        ((Tor (ModuleCat.{u} R) i).map α).app N = 0
      let c₇ := ∀ N : ModuleCat.{u} R,
        ((Tor (ModuleCat.{u} R) (e + 1)).map α).app N = 0
      List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆, c₇])

#check
  (CategoryTheory.ProjectiveResolution.liftExt_tfae α P P' e :
    let c₁ := ∃ a : P.Hom P' α, ∀ i : ℕ, e < i → a.hom.f i = 0
    let c₂ := ∃ a : P.Hom P' α, a.hom.f (e + 1) = 0
    let c₃ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      (Ext.mk₀.{u} α).precomp N (zero_add i) = 0
    let c₄ := ∀ N : ModuleCat.{u} R,
      (Ext.mk₀.{u} α).precomp N (zero_add (e + 1)) = 0
    let c₅ := (Ext.mk₀.{u} α).comp
      (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0
    List.TFAE [c₁, c₂, c₃, c₄, c₅])

#check
  (CategoryTheory.ProjectiveResolution.torVanishesAbove_of_obstruction α P' e :
    (Ext.mk₀.{u} α).comp
      (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0 →
      ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
        ((Tor (ModuleCat.{u} R) i).map α).app N = 0)

#check
  (CategoryTheory.ProjectiveResolution.torVanishesAbove_iff_succ α e :
    (∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      ((Tor (ModuleCat.{u} R) i).map α).app N = 0) ↔
      ∀ N : ModuleCat.{u} R, ((Tor (ModuleCat.{u} R) (e + 1)).map α).app N = 0)

section

variable [IsNoetherianRing R] [Module.Finite R M]

#check
  (CategoryTheory.ProjectiveResolution.liftExtTor_tfae_of_isNoetherian α P P' e :
    let c₁ := ∃ a : P.Hom P' α, ∀ i : ℕ, e < i → a.hom.f i = 0
    let c₂ := ∃ a : P.Hom P' α, a.hom.f (e + 1) = 0
    let c₃ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      (Ext.mk₀.{u} α).precomp N (zero_add i) = 0
    let c₄ := ∀ N : ModuleCat.{u} R,
      (Ext.mk₀.{u} α).precomp N (zero_add (e + 1)) = 0
    let c₅ := (Ext.mk₀.{u} α).comp
      (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0
    let c₆ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      ((Tor (ModuleCat.{u} R) i).map α).app N = 0
    let c₇ := ∀ N : ModuleCat.{u} R,
      ((Tor (ModuleCat.{u} R) (e + 1)).map α).app N = 0
    List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆, c₇])

end

#check
  (CategoryTheory.ProjectiveResolution.d_comp_factorThruImage P e :
    P.complex.d (e + 2) (e + 1) ≫
      Limits.factorThruImage (P.complex.d (e + 1) e) = 0)

#check
  (CategoryTheory.ProjectiveResolution.resolutionImageExtClass P e :
    Ext M (Limits.image (P.complex.d (e + 1) e)) (e + 1))

#check
  (CategoryTheory.ProjectiveResolution.resolutionImageExtClass_eq_extMk P e :
    P.resolutionImageExtClass e =
      P.extMk (Limits.factorThruImage (P.complex.d (e + 1) e))
        (e + 2) rfl (P.d_comp_factorThruImage e))

end CategoryTheory.ProjectiveResolution
