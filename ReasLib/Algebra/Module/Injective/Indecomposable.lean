/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Indecomposable
public import ReasLib.RingTheory.Algebra.IsEpi.Injective
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

universe u v

/-- An indecomposable injective module is an injective hull of each of its nonzero submodules. -/
theorem Module.isInjectiveHull_subtype_of_indecomposable
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (N : Submodule R E) (hN : N ≠ ⊥) :
    (Submodule.subtype N).IsInjectiveHull := sorry

/-- Any two nonzero submodules of an indecomposable injective module have nonzero intersection. -/
theorem Module.inf_ne_bot_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (M N : Submodule R E) (hM : M ≠ ⊥) (hN : N ≠ ⊥) :
    M ⊓ N ≠ ⊥ := by
  simpa only [Submodule.range_subtype] using
    (Module.isInjectiveHull_subtype_of_indecomposable R E hE M hM).essential N hN

private theorem Module.End.isUnit_iff_ker_eq_bot_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) (f : Module.End R E) :
    IsUnit f ↔ LinearMap.ker f = ⊥ := by
  constructor
  · intro hf
    exact LinearMap.ker_eq_bot_of_injective ((Module.End.isUnit_iff f).mp hf).1
  · intro hker
    have hf : Function.Injective f := LinearMap.ker_eq_bot.mp hker
    obtain ⟨g, hg⟩ := Module.Injective.out f hf (LinearMap.id : E →ₗ[R] E)
    have hgf : g.comp f = LinearMap.id := LinearMap.ext hg
    let e : (LinearMap.ker g × E) ≃ₗ[R] E :=
      lequivProdOfRightSplitExact (j := (LinearMap.ker g).subtype) (g := g) (f := f)
        (Submodule.subtype_injective _) (by simp) hgf
    let ec : ModuleCat.of R E ≅ ModuleCat.of R (LinearMap.ker g) ⊞ ModuleCat.of R E :=
      e.symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of R (LinearMap.ker g)) (ModuleCat.of R E)).symm
    rcases hE.2 _ _ ec with hzero | hzero
    · haveI : Subsingleton (LinearMap.ker g) := ModuleCat.subsingleton_of_isZero hzero
      have hgker : LinearMap.ker g = ⊥ := by
        apply (Submodule.eq_bot_iff _).mpr
        intro x hx
        exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker g) 0)
      apply (Module.End.isUnit_iff f).mpr
      refine ⟨hf, fun y => ⟨g y, ?_⟩⟩
      exact (LinearMap.ker_eq_bot.mp hgker) (hg (g y))
    · exact (hE.1 hzero).elim

/-- The endomorphism ring of an indecomposable injective module is local. -/
theorem Module.End.isLocalRing_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    IsLocalRing (Module.End R E) := by
  have hne : ¬ Subsingleton E := by
    intro h
    exact hE.1 (ModuleCat.isZero_iff_subsingleton.mpr h)
  letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hne
  letI : Nontrivial (Module.End R E) := nontrivial_of_ne 0 1 (by
    intro h01
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hx' := LinearMap.congr_fun h01 x
    exact hx (by simpa using hx'.symm))
  apply IsLocalRing.of_nonunits_add
  intro f g hf hg
  change ¬ IsUnit f at hf
  change ¬ IsUnit g at hg
  change ¬ IsUnit (f + g)
  rw [Module.End.isUnit_iff_ker_eq_bot_of_indecomposable_injective R E hE] at hf hg ⊢
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff (LinearMap.ker f ⊓ LinearMap.ker g)).mp
    (Module.inf_ne_bot_of_indecomposable_injective R E hE
      (LinearMap.ker f) (LinearMap.ker g) hf hg)
  refine (Submodule.ne_bot_iff (LinearMap.ker (f + g))).mpr ⟨z, ?_, hz0⟩
  rw [LinearMap.mem_ker, LinearMap.add_apply,
    (LinearMap.mem_ker.mp hz.1), (LinearMap.mem_ker.mp hz.2), add_zero]

/-- An endomorphism of an indecomposable injective module is a nonunit exactly when its
kernel is nonzero. -/
theorem Module.End.not_isUnit_iff_ker_ne_bot_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (f : Module.End R E) :
    ¬ IsUnit f ↔ LinearMap.ker f ≠ ⊥ :=
  not_congr (Module.End.isUnit_iff_ker_eq_bot_of_indecomposable_injective R E hE f)

/-- The ideal of scalars that annihilate a nonzero element of an indecomposable injective
module. -/
def Module.zeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) : Ideal R where
  carrier := {r | ∃ x : E, x ≠ 0 ∧ r • x = 0}
  zero_mem' := by
    have hne : ¬ Subsingleton E := by
      intro h
      exact hE.1 ((ModuleCat.isZero_iff_subsingleton).2 h)
    letI : Nontrivial E := (not_subsingleton_iff_nontrivial.mp hne)
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨x, hx, zero_smul R x⟩
  add_mem' := by
    intro r s hr hs
    rcases hr with ⟨x, hx, hxr⟩
    rcases hs with ⟨y, hy, hys⟩
    let M : Submodule R E := LinearMap.ker (LinearMap.lsmul R E r)
    let N : Submodule R E := LinearMap.ker (LinearMap.lsmul R E s)
    have hM : M ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨x, by simpa [M, LinearMap.mem_ker, LinearMap.lsmul_apply] using hxr, hx⟩
    have hN : N ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨y, by simpa [N, LinearMap.mem_ker, LinearMap.lsmul_apply] using hys, hy⟩
    have hMN : M ⊓ N ≠ ⊥ := Module.inf_ne_bot_of_indecomposable_injective R E hE M N hM hN
    obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff (M ⊓ N)).mp hMN
    refine ⟨z, hz0, ?_⟩
    have hzM : r • z = 0 := by
      change (LinearMap.lsmul R E r) z = 0
      exact hz.1
    have hzN : s • z = 0 := by
      change (LinearMap.lsmul R E s) z = 0
      exact hz.2
    simp only [add_smul, hzM, hzN, add_zero]
  smul_mem' := by
    intro c r hr
    rcases hr with ⟨x, hx, hxr⟩
    refine ⟨x, hx, ?_⟩
    change (c * r) • x = 0
    rw [mul_smul, hxr, smul_zero]

/-- Membership in `Module.zeroDivisorIdeal` means annihilating a nonzero element. -/
theorem Module.mem_zeroDivisorIdeal_iff
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) (r : R) :
    r ∈ Module.zeroDivisorIdeal R E hE ↔ ∃ x : E, x ≠ 0 ∧ r • x = 0 := by
  rfl

/-- The zero-divisor ideal of an indecomposable injective module is prime. -/
instance Module.instIsPrimeZeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    (Module.zeroDivisorIdeal R E hE).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have h1 : (1 : R) ∈ Module.zeroDivisorIdeal R E hE := by
      rw [htop]
      simp
    obtain ⟨x, hx, h1x⟩ := (Module.mem_zeroDivisorIdeal_iff R E hE 1).mp h1
    exact hx (by simpa using h1x)
  · intro a b hab
    by_cases ha : a ∈ Module.zeroDivisorIdeal R E hE
    · exact Or.inl ha
    · right
      obtain ⟨x, hx, hxab⟩ := (Module.mem_zeroDivisorIdeal_iff R E hE (a * b)).mp hab
      apply (Module.mem_zeroDivisorIdeal_iff R E hE b).mpr
      refine ⟨a • x, ?_, ?_⟩
      · intro hbx
        apply ha
        exact (Module.mem_zeroDivisorIdeal_iff R E hE a).mpr ⟨x, hx, hbx⟩
      · calc
          b • (a • x) = (b * a) • x := (mul_smul b a x).symm
          _ = (a * b) • x := by rw [mul_comm]
          _ = 0 := hxab

/-- The canonical map from an indecomposable injective module to its localization at the
zero-divisor prime is bijective. -/
theorem Module.localizedAtZeroDivisorIdeal_bijective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    Function.Bijective
      (LocalizedModule.mkLinearMap (Module.zeroDivisorIdeal R E hE).primeCompl E) := by
  let S := (Module.zeroDivisorIdeal R E hE).primeCompl
  have hunits : ∀ s : S, IsUnit (algebraMap R (Module.End R E) s) := by
    intro s
    rw [Module.End.isUnit_iff_ker_eq_bot_of_indecomposable_injective R E hE]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hx0
    exact s.2 ((Module.mem_zeroDivisorIdeal_iff R E hE s).mpr
      ⟨x, hx0, by simpa only [Module.algebraMap_end_apply] using hx⟩)
  letI : IsLocalizedModule S (LinearMap.id : E →ₗ[R] E) :=
    { map_units := hunits
      surj := fun y => ⟨(y, 1), by simp⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  let e := IsLocalizedModule.linearEquiv S (LinearMap.id : E →ₗ[R] E)
    (LocalizedModule.mkLinearMap S E)
  have he : (e : E → LocalizedModule S E) = LocalizedModule.mkLinearMap S E := by
    funext x
    exact IsLocalizedModule.linearEquiv_apply S (LinearMap.id : E →ₗ[R] E)
      (LocalizedModule.mkLinearMap S E) x
  rw [← he]
  exact e.bijective

/-- The localization of an indecomposable injective module at its zero-divisor prime is
injective over the localized ring. -/
instance Module.instInjectiveLocalizedAtZeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    Module.Injective
      (Localization.AtPrime (Module.zeroDivisorIdeal R E hE))
      (LocalizedModule.AtPrime (Module.zeroDivisorIdeal R E hE) E) := sorry
