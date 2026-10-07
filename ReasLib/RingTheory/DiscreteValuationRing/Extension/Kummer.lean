module

public import Mathlib.FieldTheory.KummerPolynomial
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Kummer root extensions of discrete valuation rings

This file owns the canonical model obtained by adjoining a `p`th root of an element of a DVR.
When the residue class of the element is not a `p`th power, the explicit root ring is the
normalization, is again a DVR, and is weakly unramified over the source.

The concrete polynomial, extension, distinguished root, and generated subalgebra are definitions;
only their mathematical properties carry proof debt.

@stack 09EX
-/

open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u

namespace DVR.Kummer

section Model

variable {A : Type u} [CommRing A]

/-- The polynomial defining the canonical `p`th-root extension of `FractionRing A`. -/
@[stacks 09EX "Kummer root polynomial"]
noncomputable def polynomial (p : ℕ) (a : A) : Polynomial (FractionRing A) :=
  X ^ p - C (algebraMap A (FractionRing A) a)

/-- The canonical extension obtained by adjoining a root of `X ^ p - a`. -/
@[stacks 09EX "Kummer root extension"]
noncomputable abbrev RootExtension (p : ℕ) (a : A) :=
  AdjoinRoot (polynomial p a)

/-- The distinguished `p`th root in the canonical root extension. -/
@[stacks 09EX "distinguished Kummer root"]
noncomputable def root (p : ℕ) (a : A) : RootExtension p a :=
  AdjoinRoot.root (polynomial p a)

/-- The explicit `A`-subalgebra `A[a^{1/p}]` inside the canonical root extension. -/
@[stacks 09EX "Kummer root ring"]
noncomputable def RootRing (p : ℕ) (a : A) : Subalgebra A (RootExtension p a) :=
  Algebra.adjoin A ({root p a} : Set (RootExtension p a))

/-- The distinguished root satisfies its defining `p`th-power equation. -/
@[stacks 09EX "Kummer root equation"]
theorem root_pow (p : ℕ) (a : A) :
    root p a ^ p = algebraMap A (RootExtension p a) a := sorry
-- Proof strategy: unfold `root` and `polynomial`, apply `AdjoinRoot.eval₂_root`, and rewrite the
-- resulting evaluation of `X ^ p - C a` with `sub_eq_zero`.

/-- The distinguished root belongs to the explicit root ring. -/
@[stacks 09EX "distinguished root membership"]
theorem root_mem_rootRing (p : ℕ) (a : A) : root p a ∈ RootRing p a := sorry
-- Proof strategy: unfold `RootRing` and use the singleton generator inclusion
-- `Algebra.subset_adjoin`.

end Model

section Residue

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue class of `a` does not lie in the range of the `p`th-power map. -/
@[stacks 09EX "residue nonpower condition"]
def IsResidueNonpower (p : ℕ) (a : A) : Prop :=
  residue A a ∉ Set.range (fun x : ResidueField A ↦ x ^ p)

/-- The residue nonpower condition in pointwise form. -/
@[stacks 09EX "pointwise residue nonpower condition"]
theorem isResidueNonpower_iff (p : ℕ) (a : A) :
    IsResidueNonpower p a ↔ ∀ x : ResidueField A, x ^ p ≠ residue A a := sorry
-- Proof strategy: unfold `IsResidueNonpower` and `Set.range`; push negation through the
-- existential and rewrite equality orientation pointwise.

end Residue

section DVR

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

/-- A residue nonpower stays outside the `p`th-power range in the fraction field. -/
@[stacks 09EX "fraction-field nonpower criterion"]
theorem not_mem_powerRange (a : A) (h : IsResidueNonpower p a) :
    algebraMap A (FractionRing A) a ∉
      Set.range (fun x : FractionRing A ↦ x ^ p) := sorry
-- Proof strategy: a hypothetical `p`th root has integral `p`th power, hence is integral by
-- `IsIntegral.of_pow`.  Use integrally closedness of the DVR to write it as `algebraMap A _ y`,
-- pull the power equality back through `IsFractionRing.injective`, and reduce it with `residue A`
-- to contradict `h`.

/-- Pointwise form of the fraction-field nonpower criterion. -/
@[stacks 09EX "pointwise fraction-field nonpower criterion"]
theorem pow_ne (a : A) (h : IsResidueNonpower p a) (x : FractionRing A) :
    x ^ p ≠ algebraMap A (FractionRing A) a := sorry
-- Proof strategy: an equality supplies the witness `x` forbidden by `not_mem_powerRange a h`.

/-- The root polynomial is irreducible when the residue class is not a `p`th power. -/
@[stacks 09EX "irreducible Kummer root polynomial"]
theorem polynomial_irreducible (a : A) (h : IsResidueNonpower p a) :
    Irreducible (polynomial p a) := sorry
-- Proof strategy: unfold `polynomial` and apply `X_pow_sub_C_irreducible_of_prime` with
-- `Fact.out`; discharge its pointwise nonpower condition with `pow_ne a h`.

/-- A residue nonpower supplies the irreducibility fact used by Mathlib's `AdjoinRoot` field
instance. -/
@[stacks 09EX "Kummer root irreducibility instance"]
instance polynomialIrreducible (a : A) [Fact (IsResidueNonpower p a)] :
    Fact (Irreducible (polynomial p a)) := sorry
-- Proof strategy: package `polynomial_irreducible a Fact.out` as the required `Fact`.

/-- The explicit root ring is integral over the source DVR. -/
@[stacks 09EX "integrality of the Kummer root ring"]
instance rootRingIsIntegral (a : A) [Fact (IsResidueNonpower p a)] :
    Algebra.IsIntegral A (RootRing p a) := sorry
-- Proof strategy: derive integrality of `root p a` from `root_pow` with `IsIntegral.of_pow`, then
-- use the standard integrality theorem for a subalgebra generated by integral elements.

/-- The canonical root extension is the fraction field of the explicit root ring. -/
@[stacks 09EX "fraction field of the Kummer root ring"]
instance rootRingIsFractionRing (a : A) [Fact (IsResidueNonpower p a)] :
    IsFractionRing (RootRing p a) (RootExtension p a) := sorry
-- Proof strategy: use `polynomialIrreducible` to install the field structure on `RootExtension`.
-- Represent each element by a polynomial in `root p a`, clear the finitely many denominators of
-- its `FractionRing A` coefficients to obtain a numerator and nonzero denominator in `RootRing`,
-- and apply `IsFractionRing.of_field`.

/-- The explicit root ring is the integral closure of the source DVR in the root extension. -/
@[stacks 09EX "Kummer root ring as integral closure"]
instance rootRingIsIntegralClosure (a : A) [Fact (IsResidueNonpower p a)] :
    IsIntegralClosure (RootRing p a) A (RootExtension p a) := sorry
-- Proof strategy: first factor the special-fiber argument used by `rootRingIsDVR` into a private
-- lemma preceding both declarations.  Its DVR conclusion makes `RootRing` integrally closed;
-- combine that with `rootRingIsIntegral`, `rootRingIsFractionRing`, and
-- `IsIntegralClosure.of_isIntegrallyClosed`.

/-- The canonical normalization is the explicit root ring `A[a^{1/p}]`. -/
@[stacks 09EX "normalization of a residue-nonpower root extension"]
theorem normalization_eq_rootRing (a : A) (h : IsResidueNonpower p a) :
    integralClosure A (RootExtension p a) = RootRing p a := sorry
-- Proof strategy: install `Fact h` and `rootRingIsIntegralClosure`.  The inclusion from the root
-- ring to the normalization follows from integrality of the distinguished root; for the reverse
-- inclusion, use `IsIntegralClosure.isIntegral_iff` elementwise and extensionality of subalgebras.

/-- The explicit root ring is a discrete valuation ring. -/
@[stacks 09EX "Kummer root ring is a DVR"]
instance rootRingIsDVR (a : A) [Fact (IsResidueNonpower p a)] :
    IsDiscreteValuationRing (RootRing p a) := sorry
-- Proof strategy: identify the special fiber of `A[root p a]` with
-- `AdjoinRoot (X ^ p - C (residue A a))`; residue nonpower makes this quotient a field, so the
-- mapped source maximal ideal is maximal.  Use finiteness and integrality to obtain Noetherianity
-- and locality, show that maximal ideal is the image of the principal source maximal ideal, and
-- conclude with clause (4) of `discreteValuationRing_tfae`.

/-- The map from the source DVR to the explicit root ring is a DVR extension. -/
@[stacks 09EX "Kummer root ring DVR extension"]
instance rootRingIsExtension (a : A) [Fact (IsResidueNonpower p a)] :
    IsExtensionOfDiscreteValuationRings A (RootRing p a) := sorry
-- Proof strategy: use `rootRingIsIntegral` for locality of the algebra map and injectivity of the
-- inclusion into the domain `RootExtension`; package these as
-- `IsExtensionOfDiscreteValuationRings` using `rootRingIsDVR`.

/-- The explicit root-ring extension is weakly unramified. -/
@[stacks 09EX "Kummer root ring is weakly unramified"]
instance rootRingWeaklyUnramified (a : A) [Fact (IsResidueNonpower p a)] :
    WeaklyUnramified A (RootRing p a) := sorry
-- Proof strategy: the special-fiber calculation in `rootRingIsDVR` identifies the target maximal
-- ideal with `Ideal.map (algebraMap A _) (maximalIdeal A)`; rewrite with
-- `weaklyUnramified_iff_map_maximalIdeal`.

/-- The canonical normalization is a discrete valuation ring. -/
@[stacks 09EX "Kummer root normalization is a DVR"]
instance normalizationIsDVR (a : A) [Fact (IsResidueNonpower p a)] :
    IsDiscreteValuationRing (integralClosure A (RootExtension p a)) := sorry
-- Proof strategy: specialize `normalization_eq_rootRing a Fact.out` and transport
-- `rootRingIsDVR` across this subalgebra equality, using proof irrelevance for the domain witness.

/-- The canonical normalization map is a DVR extension.  This remains a named theorem rather than
an instance, matching `ofFractionField` and avoiding a second global normalization-extension
owner. -/
@[stacks 09EX "Kummer root normalization DVR extension"]
theorem normalizationExtension (a : A) [Fact (IsResidueNonpower p a)] :
    IsExtensionOfDiscreteValuationRings A (integralClosure A (RootExtension p a)) := sorry
-- Proof strategy: install the field structure from `polynomialIrreducible`, the canonical domain
-- structure on the integral closure, and `normalizationIsDVR`; then use the canonical
-- integral-closure extension-of-DVR instance (or transport `rootRingIsExtension` across
-- `normalization_eq_rootRing`).

/-- Explicit-hypothesis view of the DVR structure on the root ring. -/
@[stacks 09EX "Kummer root ring DVR criterion"]
theorem rootRing_isDVR (a : A) (h : IsResidueNonpower p a) :
    -- Local instance justification (proof-local temporary data): expose the source nonpower
    -- hypothesis to the canonical root-extension instance chain for this statement only.
    let _ : Fact (IsResidueNonpower p a) := ⟨h⟩
    IsDiscreteValuationRing (RootRing p a) := sorry
-- Proof strategy: introduce the displayed `Fact h` and return `rootRingIsDVR a` by typeclass
-- inference.

/-- Explicit-hypothesis view of weak unramifiedness of the root-ring extension. -/
@[stacks 09EX "Kummer root ring weakly-unramified criterion"]
theorem rootRing_weaklyUnramified (a : A) (h : IsResidueNonpower p a) :
    -- Local instance justification (proof-local temporary data): expose the source nonpower
    -- hypothesis to the canonical root-extension instance chain for this statement only.
    let _ : Fact (IsResidueNonpower p a) := ⟨h⟩
    WeaklyUnramified A (RootRing p a) := sorry
-- Proof strategy: introduce the displayed `Fact h` and return `rootRingWeaklyUnramified a`.

/-- Explicit-hypothesis view of the DVR structure on the canonical normalization. -/
@[stacks 09EX "Kummer root normalization DVR criterion"]
theorem normalization_isDVR (a : A) (h : IsResidueNonpower p a) :
    -- Local instance justification (proof-local temporary data): expose the source nonpower
    -- hypothesis to the canonical normalization instance chain for this statement only.
    let _ : Fact (IsResidueNonpower p a) := ⟨h⟩
    IsDiscreteValuationRing (integralClosure A (RootExtension p a)) := sorry
-- Proof strategy: introduce the displayed `Fact h` and return `normalizationIsDVR a`.

/-- Explicit-hypothesis view of the canonical normalization map as a DVR extension. -/
@[stacks 09EX "Kummer root normalization DVR-extension criterion"]
theorem normalization_isExtension (a : A) (h : IsResidueNonpower p a) :
    -- Local instance justification (proof-local temporary data): expose the source nonpower
    -- hypothesis to the canonical normalization instance chain for this statement only.
    let _ : Fact (IsResidueNonpower p a) := ⟨h⟩
    IsExtensionOfDiscreteValuationRings A (integralClosure A (RootExtension p a)) := sorry
-- Proof strategy: introduce the displayed `Fact h` and apply `normalizationExtension a`.

/-- Explicit-hypothesis view of weak unramifiedness of the canonical normalization. -/
@[stacks 09EX "Kummer root normalization weakly-unramified criterion"]
theorem normalization_weaklyUnramified (a : A) (h : IsResidueNonpower p a) :
    -- Local instance justification (proof-local temporary data): expose the source nonpower
    -- hypothesis to the canonical normalization instance chain for this statement only.
    let _ : Fact (IsResidueNonpower p a) := ⟨h⟩
    -- Local instance justification (instance diamond): choose the named fraction-field
    -- normalization extension without registering a competing global instance.
    let _ : IsExtensionOfDiscreteValuationRings A (integralClosure A (RootExtension p a)) :=
      normalizationExtension a
    WeaklyUnramified A (integralClosure A (RootExtension p a)) := sorry
-- Proof strategy: install the two displayed local instances, transport
-- `rootRingWeaklyUnramified a` across `normalization_eq_rootRing a h`, and use proof irrelevance to
-- align the domain, DVR, and extension witnesses in the class-valued target.

end DVR

end DVR.Kummer
