module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Module
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The reduced diagonal over the minimal primes

The reduction of a ring maps diagonally into the product of its minimal-prime
quotients. The resulting linear map becomes surjective after localization at
each minimal prime when the minimal-prime set is finite.
-/

universe u

namespace minimalPrimes.ReducedDiagonal

variable {R : Type u} [CommRing R]

/-- The intersection of all minimal primes is the nilradical. -/
@[stacks 0BWX "minimal-prime intersection"]
theorem iInf_eq_nilradical :
    (⨅ p : _root_.minimalPrimes R, p.1) = nilradical R := by
  ext r
  rw [Ideal.mem_iInf]
  change (∀ p : _root_.minimalPrimes R, r ∈ p.1) ↔ r ∈ (⊥ : Ideal R).radical
  constructor
  · intro h
    have hr : r ∈ sInf ((⊥ : Ideal R).minimalPrimes) :=
      Ideal.mem_sInf.mpr fun p hp ↦ h ⟨p, hp⟩
    simpa only [Ideal.sInf_minimalPrimes] using hr
  · intro hr p
    have hr' : r ∈ sInf ((⊥ : Ideal R).minimalPrimes) := by
      simpa only [Ideal.sInf_minimalPrimes] using hr
    exact Ideal.mem_sInf.mp hr' p.2

/-- The canonical diagonal algebra map from the reduction to the product of
the minimal-prime quotients. -/
@[stacks 0BWX "reduced minimal-prime diagonal"]
noncomputable def algHom :
    (R ⧸ nilradical R) →ₐ[R] ∀ p : _root_.minimalPrimes R, R ⧸ p.1 :=
  AlgHom.pi fun p : _root_.minimalPrimes R ↦
    Ideal.Quotient.factorₐ R (nilradical_le_prime p.1)

/-- The reduced minimal-prime diagonal is injective. -/
@[stacks 0BWX "injectivity of the reduced minimal-prime diagonal"]
theorem algHom_injective : Function.Injective (algHom (R := R)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  swap
  · exact bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  rw [Ideal.mem_bot]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← iInf_eq_nilradical, Ideal.mem_iInf]
  intro p
  have hp := congr_fun hx p
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [algHom] using hp)

/-- On quotient generators, the reduced diagonal is the family of quotient maps. -/
@[simp, stacks 0BWX "reduced minimal-prime diagonal evaluation"]
theorem algHom_apply_mk (r : R) (p : _root_.minimalPrimes R) :
    algHom (R := R) (Ideal.Quotient.mk (nilradical R) r) p =
      Ideal.Quotient.mk p.1 r := by
  rfl

/-- The reduced diagonal as an `R`-linear map, for localization and module-theoretic API. -/
@[stacks 0BWX "linear reduced minimal-prime diagonal"]
noncomputable def linearMap :
    (R ⧸ nilradical R) →ₗ[R] ∀ p : _root_.minimalPrimes R, R ⧸ p.1 :=
  (algHom (R := R)).toLinearMap

/-- The linear reduced diagonal evaluates through the underlying ring map. -/
@[simp, stacks 0BWX "linear reduced diagonal evaluation"]
theorem linearMap_apply (x : R ⧸ nilradical R) :
    linearMap (R := R) x = algHom (R := R) x := rfl

/-- If the minimal-prime set is finite, then localizing the reduced diagonal at any minimal
prime makes it surjective. -/
@[stacks 0BWX "localized reduced diagonal with finite minimal spectrum"]
theorem localized_surjective_of_finite
    (hfinite : (_root_.minimalPrimes R).Finite)
    (q : _root_.minimalPrimes R) :
    Function.Surjective
      (LocalizedModule.map q.1.primeCompl (linearMap (R := R))) := by
  classical
  intro y
  induction y using LocalizedModule.induction_on with
  | h m s =>
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (m q)
      -- Local instance justification (proof-local temporary data): enumerate the finite set of
      -- minimal primes in order to form a denominator isolating the chosen component.
      letI : Fintype (_root_.minimalPrimes R) := hfinite.fintype
      let P := Finset.univ.erase q
      have hchoose (p : _root_.minimalPrimes R) (hp : p ∈ P) :
          ∃ a : R, a ∈ p.1 ∧ a ∉ q.1 := by
        have hpq : p ≠ q := Finset.ne_of_mem_erase hp
        have hnle : ¬ p.1 ≤ q.1 := by
          intro hpq_le
          apply hpq
          exact Subtype.ext (hpq_le.antisymm (q.2.2 p.2.1 hpq_le))
        simpa only [SetLike.not_le_iff_exists] using hnle
      choose a ha_mem ha_not_mem using
        fun p : {p : _root_.minimalPrimes R // p ∈ P} ↦ hchoose p.1 p.2
      let t : R := ∏ p : {p : _root_.minimalPrimes R // p ∈ P}, a p
      have ht_not_mem : t ∉ q.1 := by
        rw [q.2.isPrime.prod_mem_iff]
        push_neg
        intro p hp
        exact ha_not_mem p
      refine ⟨LocalizedModule.mk (Ideal.Quotient.mk (nilradical R) r) s, ?_⟩
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
      refine ⟨⟨t, ht_not_mem⟩, ?_⟩
      ext p
      by_cases hpq : p = q
      · subst p
        simp only [linearMap_apply, algHom_apply_mk, Pi.smul_apply]
        rw [hr]
      · have hpP : p ∈ P := by
          simp only [P, Finset.mem_erase, Finset.mem_univ, and_true]
          exact hpq
        have htp : t ∈ p.1 := by
          exact Ideal.prod_mem p.1 (Finset.mem_univ ⟨p, hpP⟩) (ha_mem ⟨p, hpP⟩)
        have ht_zero : Ideal.Quotient.mk p.1 t = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr htp
        simp [linearMap_apply, algHom_apply_mk, Pi.smul_apply, Submonoid.smul_def,
          Algebra.smul_def, ht_zero]

/-- Over a Noetherian ring, localization at a minimal prime makes the reduced diagonal
surjective. -/
@[stacks 0BWX "localized reduced minimal-prime diagonal"]
theorem localized_surjective [IsNoetherianRing R]
    (q : _root_.minimalPrimes R) :
    Function.Surjective
      (LocalizedModule.map q.1.primeCompl (linearMap (R := R))) := sorry

end minimalPrimes.ReducedDiagonal
