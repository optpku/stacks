module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Module
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Noetherian
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
local instance moduleCatHasExt : HasExt.{u} (ModuleCat.{u} R) :=
  instHasExtModuleCatOfSmall R

/-- For fixed module morphism and projective resolutions, the bounded lift condition, its
successor-degree form, and the corresponding Ext conditions are equivalent. -/
theorem liftExt_tfae :
    let c₁ := ∃ a : P.Hom P' α, ∀ i : ℕ, e < i → a.hom.f i = 0
    let c₂ := ∃ a : P.Hom P' α, a.hom.f (e + 1) = 0
    let c₃ := ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      (Ext.mk₀.{u} α).precomp N (zero_add i) = 0
    let c₄ := ∀ N : ModuleCat.{u} R,
      (Ext.mk₀.{u} α).precomp N (zero_add (e + 1)) = 0
    let c₅ := (Ext.mk₀.{u} α).comp
      (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0
    List.TFAE [c₁, c₂, c₃, c₄, c₅] := sorry

/-- Vanishing of the canonical resolution obstruction implies vanishing of all higher Tor maps. -/
theorem torVanishesAbove_of_obstruction
    (h : (Ext.mk₀.{u} α).comp
      (P'.resolutionImageExtClass.{u} e) (zero_add (e + 1)) = 0) :
    ∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      ((Tor (ModuleCat.{u} R) i).map α).app N = 0 := sorry

/-- The vanishing of all Tor maps above `e` is equivalent to vanishing in degree `e + 1`. -/
theorem torVanishesAbove_iff_succ :
    (∀ (N : ModuleCat.{u} R) (i : ℕ), e < i →
      ((Tor (ModuleCat.{u} R) i).map α).app N = 0) ↔
      ∀ N : ModuleCat.{u} R, ((Tor (ModuleCat.{u} R) (e + 1)).map α).app N = 0 := sorry

/-- If `M` is `(-e - 1)`-pseudo-coherent, the lift, Ext, and Tor conditions are equivalent. -/
theorem liftExtTor_tfae_of_isMPseudoCoherent
    (hM : CategoryTheory.ModuleCat.IsMPseudoCoherent M (-((e : ℤ)) - 1)) :
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
    List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆, c₇] := sorry

/-- Over a Noetherian ring, finiteness of `M` makes the lift, Ext, and Tor conditions equivalent. -/
theorem liftExtTor_tfae_of_isNoetherian [IsNoetherianRing R] [Module.Finite R M] :
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
    List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆, c₇] := sorry

end CategoryTheory.ProjectiveResolution
