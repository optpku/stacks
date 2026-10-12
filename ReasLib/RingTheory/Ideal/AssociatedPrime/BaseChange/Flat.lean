/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped.Tensor
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Regular
public import ReasLib.RingTheory.Localization.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact associated primes under flat base change

This leaf owns the prime-quotient formula for exact-annihilator associated primes.  It uses the
canonical quotient carrier `N ⧸ (p.map (algebraMap R S) • ⊤)` directly, matching Mathlib's
general-ideal API, and does not depend on the relative-assassin source presentation in Chapter 10.

@stack 0312
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right
open Module

universe u v w x

namespace associatedPrimesOfModule.BaseChange.Flat

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- A fixed exact associated prime `p` of `M` contributes all exact associated primes of
`N / pN` to the flat base change `N ⊗[R] M`. -/
@[stacks 0312 "fixed-prime flat-base-change inclusion"]
theorem quotient_subset_tensor [Module.Flat R N] {p : Ideal R}
    (hp : p ∈ associatedPrimesOfModule R M) :
    associatedPrimesOfModule S
        (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) ⊆
      associatedPrimesOfModule S (N ⊗[R] M) := by
  intro q hq
  change Ideal.IsAssociatedToModule R M p at hp
  rcases hp with ⟨_, m, hm⟩
  let f₀ : R →ₗ[R] M := (LinearMap.lsmul R M).flip m
  have hker_le : p ≤ LinearMap.ker f₀ := by
    intro r hr
    simpa [f₀, hm, Ideal.mem_torsionOf_iff] using hr
  let f : R ⧸ p →ₗ[R] M := p.liftQ f₀ hker_le
  have hker_eq : LinearMap.ker f₀ = p := by
    ext r
    simp [f₀, hm, Ideal.mem_torsionOf_iff]
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    simpa [f] using Submodule.ker_liftQ_eq_bot' p f₀ hker_eq.symm
  let fTensor : N ⊗[R] (R ⧸ p) →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N f
  have hfTensor : Function.Injective fTensor := by
    simpa [fTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf
  let e := Ideal.Quotient.Map.quotientEquivTensor (R := R) (S := S) (N := N) p
  let g : (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) →ₗ[S]
      N ⊗[R] M := fTensor.comp e.toLinearMap
  have hg : Function.Injective g := hfTensor.comp e.injective
  change Ideal.IsAssociatedToModule S _ q at hq ⊢
  rcases hq with ⟨hqPrime, z, hz⟩
  refine ⟨hqPrime, g z, hz.trans ?_⟩
  ext r
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro hr
    simpa using congrArg g hr
  · intro hr
    exact hg (by simpa using hr)

/-- Taking the union of `quotient_subset_tensor` over all exact associated primes of `M`. -/
@[stacks 0312 "(1), flat-base-change inclusion"]
theorem iUnion_quotient_subset [Module.Flat R N] :
    (⋃ p ∈ associatedPrimesOfModule R M,
      associatedPrimesOfModule S
        (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      associatedPrimesOfModule S (N ⊗[R] M) :=
  Set.iUnion₂_subset fun _ hp ↦ quotient_subset_tensor hp

/-- The prime-quotient union is monotone under an injective map of source modules. -/
private theorem iUnion_quotient_subset_of_injective
    {M' : Type*} [AddCommGroup M'] [Module R M']
    {f : M' →ₗ[R] M} (hf : Function.Injective f) :
    (⋃ p ∈ associatedPrimesOfModule R M',
      associatedPrimesOfModule S
        (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      ⋃ p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  intro q hq
  rcases Set.mem_iUnion.mp hq with ⟨p, hq⟩
  rcases Set.mem_iUnion.mp hq with ⟨hp, hq⟩
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
    ⟨associatedPrimesOfModule.subset_of_injective hf hp, hq⟩⟩

/-- Every exact associated-prime witness in a tensor product is already carried by a finite
source submodule. -/
private theorem associatedPrime_tensor_exists_finite_submodule [Module.Flat R N]
    {q : Ideal S} (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    ∃ (M' : Submodule R M) (_ : Module.Finite R M'),
      q ∈ associatedPrimesOfModule S (N ⊗[R] M') := by
  change Ideal.IsAssociatedToModule S (N ⊗[R] M) q at hq
  rcases hq with ⟨hqPrime, x, hx⟩
  obtain ⟨M', hM'finite, hx_range⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite
      (R := R) (M := N) (N := M) ({x} : Set (N ⊗[R] M)) (Set.toFinite _)
  let inclusionTensor : N ⊗[R] M' →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype
  have hx_mem_range : x ∈ LinearMap.range inclusionTensor := by
    simpa [inclusionTensor] using hx_range (by simp)
  rcases hx_mem_range with ⟨x', rfl⟩
  refine ⟨M', hM'finite, hqPrime, x', ?_⟩
  have hinjective : Function.Injective inclusionTensor := by
    simpa [inclusionTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := N) M'.subtype
        (Submodule.injective_subtype M')
  calc
    q = Ideal.torsionOf S (N ⊗[R] M) (inclusionTensor x') := by
      simpa [hx, inclusionTensor]
    _ = Ideal.torsionOf S (N ⊗[R] M') x' :=
      Ideal.torsionOf_map_eq_of_injective hinjective x'

/-- Tensoring the right-factor scalar-multiplication map is scalar multiplication on the tensor
product. -/
private theorem localized_lTensor_lsmul_eq_lsmul
    (q : PrimeSpectrum S) (r : R) :
    (TensorProduct.AlgebraTensorModule.lTensor (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal N)
        (LinearMap.lsmul R (LocalizedModule.AtPrime (q.asIdeal.under R) M) r)).restrictScalars R =
      LinearMap.lsmul R
        (LocalizedModule.AtPrime q.asIdeal N ⊗[R]
          LocalizedModule.AtPrime (q.asIdeal.under R) M) r := by
  ext x y
  simp [LinearMap.lsmul_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- A regular localized element in the maximal ideal has a numerator in the original prime that
acts regularly on the localized module. -/
private theorem exists_mem_isSMulRegular_atPrime_numerator
    {p : Ideal R} [p.IsPrime] {x : Localization.AtPrime p}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hreg : IsSMulRegular (LocalizedModule.AtPrime p M) x) :
    ∃ r ∈ p, IsSMulRegular (LocalizedModule.AtPrime p M) r := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  have hrp : r ∈ p :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff
      (S := Localization.AtPrime p) (I := p) r s).mp hx
  have hsreg :
      IsSMulRegular (LocalizedModule.AtPrime p M)
        (algebraMap R (Localization.AtPrime p) (s : R)) :=
    (IsLocalization.map_units (Localization.AtPrime p) s).isSMulRegular _
  have hmap :
      IsSMulRegular (LocalizedModule.AtPrime p M)
        (algebraMap R (Localization.AtPrime p) r) := by
    rw [← (IsLocalization.mk'_spec (M := p.primeCompl)
      (S := Localization.AtPrime p) r s)]
    exact hreg.mul hsreg
  exact ⟨r, hrp, (isSMulRegular_algebraMap_iff
    (A := Localization.AtPrime p) (M := LocalizedModule.AtPrime p M) (r := r)).mp hmap⟩

/-- In the finite Noetherian case, an exact associated prime after flat tensor base change
contracts to an exact associated prime of the source module. -/
private theorem under_mem_associatedPrimesOfModule_of_mem_tensor_of_finite
    [Module.Flat R N] [IsNoetherianRing R] [Module.Finite R M]
    {q : Ideal S} [q.IsPrime]
    (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    q.under R ∈ associatedPrimesOfModule R M := by
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  let p : Ideal R := q.under R
  letI : p.IsPrime := Ideal.IsPrime.under (A := R) q
  have hq_local :
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ∈
        associatedPrimesOfModule (Localization.AtPrime q)
          (LocalizedModule.AtPrime q (N ⊗[R] M)) :=
    associatedPrimesOfModule.Localization.maximalIdeal_mem_atPrime hq
  by_contra hp_not
  have hp_local_not_text :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
        associatedPrimesOfModule (Localization.AtPrime p)
          (LocalizedModule.AtPrime p M) := by
    intro hp_local
    exact hp_not <| associatedPrimesOfModule.Localization.mem_of_maximalIdeal_mem_atPrime
      hp_local p.fg_of_isNoetherianRing
  have hp_local_not :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
        associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp_local_not_text
  have hmax_not_le :
      ∀ J ∈ associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M),
        ¬ IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤ J := by
    intro J hJ hle
    letI : J.IsPrime := hJ.1
    have hJ_le : J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
      IsLocalRing.le_maximalIdeal_of_isPrime J
    exact hp_local_not (le_antisymm hJ_le hle ▸ hJ)
  obtain ⟨x, hxmax, hreg_x⟩ :=
    (Ideal.exists_isSMulRegular_iff_not_le_associatedPrimes
      (R := Localization.AtPrime p)
      (M := LocalizedModule.AtPrime p M)
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime p))).2 hmax_not_le
  obtain ⟨r, hrp, hreg_r⟩ :=
    exists_mem_isSMulRegular_atPrime_numerator
      (R := R) (M := M) (p := p) hxmax hreg_x
  have hNq_flat : Module.Flat R (LocalizedModule.AtPrime q N) :=
    Module.Flat.localizedModule_of_tower
      (R := R) (A := S) (M := N) q.primeCompl inferInstance
  letI : Module.Flat R (LocalizedModule.AtPrime q N) := hNq_flat
  have hreg_tensor :
      IsSMulRegular
        (LocalizedModule.AtPrime q N ⊗[R] LocalizedModule.AtPrime p M) r := by
    have hTensor_inj :
        Function.Injective
          ((TensorProduct.AlgebraTensorModule.lTensor (Localization.AtPrime q)
              (LocalizedModule.AtPrime q N)
              (LinearMap.lsmul R (LocalizedModule.AtPrime p M) r)).restrictScalars R) := by
      simpa using
        Module.Flat.lTensor_preserves_injective_linearMap
          (M := LocalizedModule.AtPrime q N)
          (LinearMap.lsmul R (LocalizedModule.AtPrime p M) r) hreg_r
    rw [localized_lTensor_lsmul_eq_lsmul
      (R := R) (S := S) (M := M) (N := N) q' r] at hTensor_inj
    exact hTensor_inj
  have hreg_localized :
      IsSMulRegular (LocalizedModule.AtPrime q (N ⊗[R] M)) r := by
    let e := LocalizedModule.AtPrime.tensorProductUnderLinearEquiv
      (R := R) (A := S) (X := N) M q'
    exact (e.toEquiv.isSMulRegular_congr (e.map_smul r)).1 hreg_tensor
  have hreg_localized_sq :
      IsSMulRegular (LocalizedModule.AtPrime q (N ⊗[R] M))
        (algebraMap R (Localization.AtPrime q) r) :=
    (isSMulRegular_algebraMap_iff
      (A := Localization.AtPrime q)
      (M := LocalizedModule.AtPrime q (N ⊗[R] M))).2 hreg_localized
  have hr_mem_max :
      algebraMap R (Localization.AtPrime q) r ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    simpa [p, Ideal.under_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)] using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime q) q (algebraMap R S r)).2 hrp
  change Ideal.IsAssociatedToModule (Localization.AtPrime q)
    (LocalizedModule.AtPrime q (N ⊗[R] M))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) at hq_local
  rcases hq_local with ⟨hqmax_prime, z, hz⟩
  have hr_torsion :
      algebraMap R (Localization.AtPrime q) r ∈
        Ideal.torsionOf (Localization.AtPrime q)
          (LocalizedModule.AtPrime q (N ⊗[R] M)) z := by
    simpa [hz] using hr_mem_max
  have hsmul_zero : (algebraMap R (Localization.AtPrime q) r) • z = 0 := by
    simpa [Ideal.mem_torsionOf_iff] using hr_torsion
  have hz_zero : z = 0 := hreg_localized_sq (by simpa using hsmul_zero)
  have htop : IsLocalRing.maximalIdeal (Localization.AtPrime q) = ⊤ := by
    rw [hz, hz_zero, Ideal.torsionOf_zero]
  exact hqmax_prime.ne_top htop

/-- Tensoring a prime filtration with a flat module puts every exact associated prime in some
tensorized prime-quotient branch. -/
private theorem tensor_subset_iUnion_primeQuotients_of_filtration
    [Module.Flat R N] (s : PrimeFiltration R M) (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule S (N ⊗[R] s.last) ⊆
      ⋃ p : PrimeSpectrum R,
        associatedPrimesOfModule S
          (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton K =>
      intro hs₀ q hq
      have hK : K = ⊥ := by simpa using hs₀
      subst K
      change Ideal.IsAssociatedToModule S (N ⊗[R] (⊥ : Submodule R M)) q at hq
      rcases hq with ⟨hqPrime, z, hz⟩
      letI : Subsingleton (N ⊗[R] (⊥ : Submodule R M)) := inferInstance
      have hz_zero : z = 0 := Subsingleton.elim _ _
      have htop : q = ⊤ := by rw [hz, hz_zero, Ideal.torsionOf_zero]
      exact (hqPrime.ne_top htop).elim
  | snoc s K hrel ih =>
      rcases hrel with ⟨hle, p, hp⟩
      intro hs₀ q hq
      let f : N ⊗[R] (s.last.submoduleOf K) →ₗ[S] N ⊗[R] K :=
        TensorProduct.AlgebraTensorModule.lTensor S N (s.last.submoduleOf K).subtype
      let g : N ⊗[R] K →ₗ[S] N ⊗[R] (K ⧸ s.last.submoduleOf K) :=
        TensorProduct.AlgebraTensorModule.lTensor S N ((s.last.submoduleOf K).mkQ)
      have hf : Function.Injective f := by
        simpa [f] using
          Module.Flat.lTensor_preserves_injective_linearMap (M := N)
            (s.last.submoduleOf K).subtype
            (Submodule.injective_subtype (s.last.submoduleOf K))
      have hfg : Function.Exact f g := by
        simpa [f, g] using
          (lTensor_exact N (LinearMap.exact_subtype_mkQ (s.last.submoduleOf K))
            (Submodule.mkQ_surjective (s.last.submoduleOf K)))
      have hsubset :
          associatedPrimesOfModule S (N ⊗[R] K) ⊆
            associatedPrimesOfModule S (N ⊗[R] (s.last.submoduleOf K)) ∪
              associatedPrimesOfModule S (N ⊗[R] (K ⧸ s.last.submoduleOf K)) :=
        associatedPrimesOfModule.subset_union_of_exact hf hfg
      have hqK : q ∈ associatedPrimesOfModule S (N ⊗[R] K) := by
        rw [RelSeries.last_snoc] at hq
        exact hq
      rcases hsubset hqK with hq_prev | hq_last
      · have hq_prev_last : q ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
          let e := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N)
            (Submodule.submoduleOfEquivOfLe hle)
          rw [← e.associatedPrimesOfModule_eq]
          exact hq_prev
        exact ih hs₀ hq_prev_last
      · rcases hp with ⟨e⟩
        have hq_tensor_quotient :
            q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) := by
          let eTensor := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e
          rw [← eTensor.associatedPrimesOfModule_eq]
          exact hq_last
        have hq_prime_quotient :
            q ∈ associatedPrimesOfModule S
              (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N))) := by
          let eQuot := Ideal.Quotient.Map.quotientEquivTensor
            (R := R) (S := S) (N := N) p.asIdeal
          rw [eQuot.associatedPrimesOfModule_eq]
          exact hq_tensor_quotient
        exact Set.mem_iUnion.mpr ⟨p, hq_prime_quotient⟩

/-- The Noetherian converse for a finite source module. -/
private theorem tensor_subset_iUnion_quotient_of_finite
    [Module.Flat R N] [IsNoetherianRing R] [Module.Finite R M] :
    associatedPrimesOfModule S (N ⊗[R] M) ⊆
      ⋃ p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  intro q hq
  letI : q.IsPrime := hq.1
  have hunder : q.under R ∈ associatedPrimesOfModule R M :=
    under_mem_associatedPrimesOfModule_of_mem_tensor_of_finite
      (R := R) (S := S) (M := M) (N := N) hq
  obtain ⟨s, hs₀, hs_top⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime (A := R) (M := M)
  let eTop : s.last ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ hs_top).trans Submodule.topEquiv
  have hq_last : q ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
    let e := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) eTop
    rw [e.associatedPrimesOfModule_eq]
    exact hq
  rcases Set.mem_iUnion.mp
      (tensor_subset_iUnion_primeQuotients_of_filtration
        (R := R) (S := S) (M := M) (N := N) s hs₀ hq_last) with ⟨p, hq_branch⟩
  have hq_tensor_quotient :
      q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) := by
    let e := Ideal.Quotient.Map.quotientEquivTensor
      (R := R) (S := S) (N := N) p.asIdeal
    rw [← e.associatedPrimesOfModule_eq]
    exact hq_branch
  have hunder_branch :
      q.under R ∈ associatedPrimesOfModule R (R ⧸ p.asIdeal) :=
    under_mem_associatedPrimesOfModule_of_mem_tensor_of_finite
      (R := R) (S := S) (M := R ⧸ p.asIdeal) (N := N) hq_tensor_quotient
  have hunder_eq : q.under R = p.asIdeal := by
    rw [associatedPrimesOfModule.quotient_prime_eq_singleton,
      Set.mem_singleton_iff] at hunder_branch
    exact hunder_branch
  exact Set.mem_iUnion.mpr ⟨q.under R, Set.mem_iUnion.mpr
    ⟨hunder, hunder_eq.symm ▸ hq_branch⟩⟩

/-- Over a Noetherian base, every exact associated prime of the flat base change comes from a
prime-quotient branch. -/
@[stacks 0312 "Noetherian flat-base-change converse"]
theorem tensor_subset_iUnion_quotient
    [Module.Flat R N] [IsNoetherianRing R] :
    associatedPrimesOfModule S (N ⊗[R] M) ⊆
      ⋃ p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  intro q hq
  obtain ⟨M', hM'finite, hq'⟩ :=
    associatedPrime_tensor_exists_finite_submodule
      (R := R) (S := S) (M := M) (N := N) hq
  have hq_finite :
      q ∈ ⋃ p ∈ associatedPrimesOfModule R M',
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) :=
    tensor_subset_iUnion_quotient_of_finite
      (R := R) (S := S) (M := M') (N := N) hq'
  exact iUnion_quotient_subset_of_injective
    (R := R) (S := S) (M := M) (N := N)
    (f := M'.subtype) (Submodule.injective_subtype M') hq_finite

/-- Over a Noetherian base, exact associated primes of `N ⊗[R] M` are precisely those of
`N / pN` as `p` ranges over the exact associated primes of `M`. -/
@[stacks 0312 "(2), Noetherian equality"]
theorem tensor_eq_iUnion_quotient
    [Module.Flat R N] [IsNoetherianRing R] :
    associatedPrimesOfModule S (N ⊗[R] M) =
      ⋃ p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) :=
  Set.Subset.antisymm tensor_subset_iUnion_quotient iUnion_quotient_subset

end associatedPrimesOfModule.BaseChange.Flat
