module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity

/-!
# Complementary Powers in Two-Periodic Endomorphism Complexes

This file constructs the two-periodic complex associated to complementary powers of a
nilpotent module endomorphism and studies its homology lengths and multiplicity.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The first complementary power followed by the second is zero. -/
theorem ofPowers_d₀_d₁ (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n)
    (hnil : φ ^ n = 0) :
    ModuleCat.ofHom (φ ^ i) ≫ ModuleCat.ofHom (φ ^ (n - i)) = 0 := sorry

/-- The second complementary power followed by the first is zero. -/
theorem ofPowers_d₁_d₀ (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n)
    (hnil : φ ^ n = 0) :
    ModuleCat.ofHom (φ ^ (n - i)) ≫ ModuleCat.ofHom (φ ^ i) = 0 := sorry

/-- The two-periodic endomorphism complex with differentials `φ ^ i` and `φ ^ (n - i)`. -/
def ofPowers (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n) (hnil : φ ^ n = 0) :
    TwoPeriodicEndomorphism (ModuleCat R) where
  X := ModuleCat.of R M
  d₀ := ModuleCat.ofHom (φ ^ i)
  d₁ := ModuleCat.ofHom (φ ^ (n - i))
  d₀_d₁ := ofPowers_d₀_d₁ φ n i hi hnil
  d₁_d₀ := ofPowers_d₁_d₀ φ n i hi hnil

/-- The underlying module of the complementary-power complex is `M`. -/
@[simp]
theorem ofPowers_X (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n) (hnil : φ ^ n = 0) :
    (ofPowers φ n i hi hnil).X = ModuleCat.of R M := sorry

/-- The degree-zero differential of the complementary-power complex is `φ ^ i`. -/
@[simp]
theorem ofPowers_d₀ (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n) (hnil : φ ^ n = 0) :
    (ofPowers φ n i hi hnil).d₀ = ModuleCat.ofHom (φ ^ i) := sorry

/-- The degree-one differential of the complementary-power complex is `φ ^ (n - i)`. -/
@[simp]
theorem ofPowers_d₁ (φ : Module.End R M) (n i : ℕ) (hi : i ≤ n) (hnil : φ ^ n = 0) :
    (ofPowers φ n i hi hnil).d₁ = ModuleCat.ofHom (φ ^ (n - i)) := sorry

/-- Finite length of `ker φ / range (φ ^ (n - 1))` implies finite length of degree-zero
homology for every complementary-power complex. -/
theorem ofPowers_homology_zero_isFiniteLength (φ : Module.End R M) (n : ℕ) (hn : 0 < n)
    (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R (φ.ker ⧸ (φ ^ (n - 1)).range.submoduleOf φ.ker))
    (i : ℕ) (hi : i ≤ n) :
    IsFiniteLength R ((ofPowers φ n i hi hnil).toCochainComplex.homology 0) := sorry

/-- Finite length of `ker φ / range (φ ^ (n - 1))` implies finite length of degree-one
homology for every complementary-power complex. -/
theorem ofPowers_homology_one_isFiniteLength (φ : Module.End R M) (n : ℕ) (hn : 0 < n)
    (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R (φ.ker ⧸ (φ ^ (n - 1)).range.submoduleOf φ.ker))
    (i : ℕ) (hi : i ≤ n) :
    IsFiniteLength R ((ofPowers φ n i hi hnil).toCochainComplex.homology 1) := sorry

/-- A nilpotent endomorphism whose first kernel modulo the penultimate power's range has
finite length gives multiplicity zero for every pair of complementary powers. -/
theorem eulerMultiplicity_ofPowers_eq_zero (φ : Module.End R M) (n : ℕ) (hn : 0 < n)
    (hnil : φ ^ n = 0)
    (hfinite : IsFiniteLength R (φ.ker ⧸ (φ ^ (n - 1)).range.submoduleOf φ.ker))
    (i : ℕ) (hi : i ≤ n) :
    (ofPowers φ n i hi hnil).multiplicity
      (ofPowers_homology_zero_isFiniteLength φ n hn hnil hfinite i hi)
      (ofPowers_homology_one_isFiniteLength φ n hn hnil hfinite i hi) = 0 := sorry

end CategoryTheory.TwoPeriodicEndomorphism
