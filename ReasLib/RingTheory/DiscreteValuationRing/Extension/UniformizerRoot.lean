/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensions obtained by adjoining a root of a uniformizer

This leaf owns the concrete polynomial, quotient ring, fraction-field model,
and distinguished root used to adjoin an `n`th root of a DVR uniformizer.
The arithmetic declarations expose the integral-closure, ramification, and
intermediate-field properties of that model.

@stack 09EV
@stack 0EXW
-/

@[expose] public section

open Polynomial Ideal IsLocalRing Algebra
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

noncomputable section

namespace DVR.UniformizerRoot

section Model

variable {A : Type u} [CommRing A]

/-- The polynomial `X ^ n - C π` defining the root ring. -/
@[stacks 09EV "uniformizer-root polynomial"]
abbrev polynomial (π : A) (n : ℕ) : A[X] := X ^ n - C π

/-- The explicit quotient ring `A[π^(1/n)]`. -/
@[stacks 09EV "uniformizer-root extension ring"]
abbrev RootRing (π : A) (n : ℕ) : Type u := AdjoinRoot (polynomial π n)

/-- The defining polynomial after base change to `FractionRing A`. -/
@[stacks 09EV "uniformizer-root fraction polynomial"]
abbrev fractionPolynomial (π : A) (n : ℕ) : (FractionRing A)[X] :=
  (polynomial π n).map (algebraMap A (FractionRing A))

/-- The canonical fraction-field extension containing the distinguished root. -/
@[stacks 09EV "uniformizer-root field extension"]
abbrev RootExtension (π : A) (n : ℕ) : Type u :=
  AdjoinRoot (fractionPolynomial π n)

/-- The distinguished root in the fraction-field extension. -/
@[stacks 09EV "distinguished uniformizer root"]
abbrev root (π : A) (n : ℕ) : RootExtension π n :=
  AdjoinRoot.root (fractionPolynomial π n)

/-- The canonical fraction-field algebra on the root extension. -/
@[stacks 09EV "uniformizer-root fraction-field algebra"]
instance fractionAlgebra {π : A} {n : ℕ} :
    Algebra (FractionRing A) (RootExtension π n) :=
  AdjoinRoot.instAlgebra (fractionPolynomial π n)

/-- The base-ring algebra induced through `FractionRing A`. -/
@[stacks 09EV "uniformizer-root base algebra"]
instance baseAlgebra {π : A} {n : ℕ} : Algebra A (RootExtension π n) :=
  Algebra.compHom (RootExtension π n) (algebraMap A (FractionRing A))

/-- The distinguished root satisfies its defining power equation. -/
@[stacks 09EV "distinguished uniformizer-root equation"]
theorem root_pow {π : A} {n : ℕ} :
    root π n ^ n = algebraMap A (RootExtension π n) π := sorry
-- Proof strategy: specialize `AdjoinRoot.isRoot_root` to `fractionPolynomial π n`, then unfold
-- `root`, `fractionPolynomial`, and `polynomial`; evaluation of `X ^ n - C π` gives exactly the
-- displayed power equation after simplifying the two algebra maps.

/-- The canonical scalar tower through the fraction field. -/
@[stacks 09EV "uniformizer-root scalar tower"]
instance scalarTower {π : A} {n : ℕ} :
    IsScalarTower A (FractionRing A) (RootExtension π n) := sorry
-- Proof strategy: use `IsScalarTower.of_algebraMap_eq'`; `baseAlgebra` was defined by
-- `Algebra.compHom`, so the required equality of algebra maps is definitional after extensionality.

/-- The explicit root ring acts on the fraction-field root extension. -/
@[stacks 09EV "root-ring algebra on the root extension"]
instance rootRingAlgebra {π : A} {n : ℕ} :
    Algebra (RootRing π n) (RootExtension π n) :=
  (AdjoinRoot.map (algebraMap A (FractionRing A)) (polynomial π n)
    (fractionPolynomial π n) dvd_rfl).toAlgebra

/-- The canonical scalar tower through the explicit root ring. -/
@[stacks 09EV "root-ring scalar tower"]
instance rootRingScalarTower {π : A} {n : ℕ} :
    IsScalarTower A (RootRing π n) (RootExtension π n) := sorry
-- Proof strategy: apply `IsScalarTower.of_algebraMap_eq'` and use the commutation formula for
-- `AdjoinRoot.map`; on coefficients the composite is `algebraMap A (FractionRing A)` and on the
-- distinguished root both sides are `AdjoinRoot.root (fractionPolynomial π n)`.

end Model

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "A[" π "^(1/" n ")]" =>
  DVR.UniformizerRoot.RootRing π n

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "K[" π "^(1/" n ")]" =>
  DVR.UniformizerRoot.RootExtension π n

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "root[" π "^(1/" n ")]" =>
  DVR.UniformizerRoot.root π n

open scoped UniformizerRoot

section DVR

variable {A : Type u} [CommRing A]

/-- A uniformizer-root polynomial remains irreducible over the fraction field. -/
@[stacks 09EV "irreducibility of the uniformizer-root polynomial"]
theorem fractionPolynomial_irreducible [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    (hπ : Irreducible π) (hn : n ≠ 0) :
    Irreducible (fractionPolynomial π n) := sorry
-- Proof strategy: show `polynomial π n = X ^ n - C π` is Eisenstein at `maximalIdeal A`.
-- Irreducibility of `π` in a DVR identifies its principal ideal with the maximal ideal, so the
-- constant coefficient lies in the maximal ideal but not its square; all other lower coefficients
-- vanish and the leading coefficient is one.  Apply `Polynomial.irreducible_of_eisenstein_criterion`
-- and transport the result to the mapped polynomial over `FractionRing A`.

/-- The irreducibility fact used by Mathlib's canonical `AdjoinRoot` field instance. -/
@[stacks 09EV "uniformizer-root irreducibility instance"]
instance fractionPolynomialIrreducible [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n] :
    Fact (Irreducible (fractionPolynomial π n)) := sorry
-- Proof strategy: construct the `Fact` with `fractionPolynomial_irreducible Fact.out
-- (NeZero.ne n)`.

/-- The root extension has degree `n` when the exponent is at least two. -/
@[stacks 09EV "(1) degree of the uniformizer-root extension"]
theorem finrank_eq [IsDomain A] [IsDiscreteValuationRing A] {π : A} {n : ℕ}
    (hπ : Irreducible π) (hn : 2 ≤ n) :
    Module.finrank (FractionRing A) (RootExtension π n) = n := sorry
-- Proof strategy: install the irreducibility fact from `hπ` and `hn.ne'`, use the canonical
-- `AdjoinRoot.powerBasis`, and rewrite its dimension as the natDegree of
-- `fractionPolynomial π n`.  Monicity and `2 ≤ n` reduce that natDegree to `n`.

/-- The root extension is finite-dimensional whenever `n` is nonzero. -/
@[stacks 09EV "uniformizer-root finite-dimensionality"]
instance finiteDimensional [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ} [NeZero n] :
    FiniteDimensional (FractionRing A) (RootExtension π n) := sorry
-- Proof strategy: use the finite spanning family `1, root, ..., root^(n-1)` supplied by the monic
-- `AdjoinRoot` power basis; `NeZero n` guarantees the defining polynomial has positive degree.

/-- The explicit root ring is a domain under the irreducibility hypotheses. -/
@[stacks 09EV "uniformizer-root ring domain"]
instance rootRingIsDomain [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n] : IsDomain (RootRing π n) := sorry
-- Proof strategy: map `RootRing π n` to `RootExtension π n` with `AdjoinRoot.map`.  The mapped
-- defining polynomial is irreducible, hence its quotient is a field; injectivity of the coefficient
-- map and the quotient normal forms make the induced map injective.  Pull the no-zero-divisors and
-- nontrivial structures back along this embedding.

/-- The explicit root ring is the integral closure in the root extension. -/
@[stacks 09EV "(2) uniformizer-root integral closure"]
theorem rootRing_isIntegralClosure [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ} (hπ : Irreducible π) (hn : 2 ≤ n) :
    IsIntegralClosure (RootRing π n) A (RootExtension π n) := sorry
-- Proof strategy: use the power basis `1, root, ..., root^(n-1)` and the Eisenstein property of
-- `X^n - π`.  The quotient ring is integral over `A`; conversely, for an element of the root field
-- integral over `A`, compare the valuations of its power-basis coefficients.  A negative minimal
-- coefficient valuation would make the integral equation's term of least valuation unique,
-- contradiction.  Thus every coefficient lies in the DVR `A`, so the element lies in `RootRing`.

/-- The explicit root extension is the fraction field of its root ring. -/
@[stacks 09EV "uniformizer-root fraction-field bridge"]
theorem rootRing_isFractionRing [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n]
    (hπ : Irreducible π) (hn : 0 < n) :
    IsFractionRing (RootRing π n) (RootExtension π n) := sorry
-- Proof strategy: use the explicit `AdjoinRoot.map` as the algebra map.  Its injectivity follows
-- from the two irreducibility facts.  Write an element of the fraction-field AdjoinRoot in its
-- power-basis normal form and clear the finitely many denominators of its `FractionRing A`
-- coefficients; the common denominator comes from a non-zero-divisor of `RootRing`, proving the
-- localization surjectivity condition.

/-- The canonical fraction-field instance for the explicit root ring. -/
@[stacks 09EV "uniformizer-root fraction-field instance"]
instance rootRingIsFractionRing [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n] :
    IsFractionRing (RootRing π n) (RootExtension π n) := sorry
-- Proof strategy: apply `rootRing_isFractionRing` with `Fact.out` and `NeZero.pos n`.

/-- The canonical DVR instance on the explicit root ring. -/
@[stacks 09EV "uniformizer-root ring DVR instance"]
instance rootRingIsDVR [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n] :
    IsDiscreteValuationRing (RootRing π n) := sorry
-- Proof strategy: use `root_pow` and the Eisenstein normal form to show that the root ring is local
-- with maximal ideal generated by the distinguished root.  The coefficient-valuation argument
-- makes every nonzero ideal a power of this principal maximal ideal; combine this PID property,
-- the domain instance, and nonfieldness in `IsDiscreteValuationRing.TFAE`.

/-- The explicit root ring is a discrete valuation ring under the irreducibility hypotheses. -/
@[stacks 09EV "(3) uniformizer-root ring is a DVR"]
theorem rootRing_isDVR [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ} [Fact (Irreducible π)] [NeZero n]
    (hπ : Irreducible π) (hn : 2 ≤ n) :
    IsDiscreteValuationRing (RootRing π n) := sorry
-- Proof strategy: invoke the canonical `rootRingIsDVR` instance; `hπ` and `hn` provide the same
-- irreducibility and nonzero-exponent facts explicitly for the source-facing theorem.

/-- The canonical map into the root ring is an extension of DVRs. -/
@[stacks 09EV "uniformizer-root DVR extension"]
instance rootRingIsExtension [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n] :
    IsExtensionOfDiscreteValuationRings A (RootRing π n) := sorry
-- Proof strategy: injectivity is the coefficient-map part of `rootRingIsDomain`.  Identify the
-- target maximal ideal with the span of the distinguished root and use `root_pow` plus the source
-- maximal ideal generated by `π` to show that the algebra map is local.  Package these as the two
-- fields of `IsExtensionOfDiscreteValuationRings`.

/-- The root-ring extension has ramification index `n`. -/
@[stacks 09EV "(4) uniformizer-root ramification index"]
theorem ramificationIndex_eq [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    [Fact (Irreducible π)] [NeZero n]
    (hπ : Irreducible π) (hn : 2 ≤ n) :
    ramificationIndex A (RootRing π n) = n := sorry
-- Proof strategy: identify `maximalIdeal A` with `Ideal.span {π}` and the target maximal ideal with
-- the span of the distinguished root.  The equation `root_pow` then gives
-- `map (maximalIdeal A) = maximalIdeal (RootRing π n) ^ n`; apply
-- `IsExtensionOfDiscreteValuationRings.ramificationIndex_eq_of_map_maximalIdeal_eq_pow`.

/-- The fraction-field root extension is totally ramified. -/
@[stacks 09EV "(5) total ramification of the uniformizer-root extension"]
theorem isTotallyRamified [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    {hField : Field (RootExtension π n)}
    {hA : Algebra A (RootExtension π n)}
    {hK : Algebra (FractionRing A) (RootExtension π n)}
    {hTower : @IsScalarTower A (FractionRing A) (RootExtension π n)
      _ hK.toSMul hA.toSMul}
    (hπ : Irreducible π) (hn : 2 ≤ n) :
    @DVR.Field.IsTotallyRamified A (FractionRing A) (RootExtension π n)
      _ _ _ _ _ _ hField hA hK hTower := sorry
-- Proof strategy: transport `rootRing_isIntegralClosure` to identify the integral closure with the
-- explicit local root ring, giving the unique branch.  Modulo its root-generated maximal ideal the
-- distinguished root vanishes and only the constant coefficient remains, so the residue-field map
-- is the base DVR residue map and is bijective.  Package branch uniqueness and this bijection in
-- `DVR.Field.IsTotallyRamified` for the supplied compatible scalar structures.

/-- A root extension of degree prime to the residue characteristic is tamely ramified. -/
@[stacks 09EV "(6a) tame ramification of the uniformizer-root extension"]
theorem isTamelyRamified [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    {hField : Field (RootExtension π n)}
    {hA : Algebra A (RootExtension π n)}
    {hK : Algebra (FractionRing A) (RootExtension π n)}
    {hTower : @IsScalarTower A (FractionRing A) (RootExtension π n)
      _ hK.toSMul hA.toSMul}
    (hπ : Irreducible π) (hn : 2 ≤ n)
    (hprime : DVR.Field.PrimeToResidueChar A n) :
    @DVR.Field.IsTamelyRamified A (FractionRing A) (RootExtension π n)
      _ _ _ _ _ _ hField hA hK hTower := sorry
-- Proof strategy: use `isTotallyRamified` to obtain the unique branch and a residue-field
-- equivalence, hence residue separability.  Rewrite its ramification index with
-- `ramificationIndex_eq`; `hprime` is exactly the required coprimality with every residue
-- characteristic.  Assemble the two fields of `DVR.Field.IsTamelyRamified`.

/-- Under the tame hypothesis, every intermediate field is generated by a power of the
distinguished root. -/
@[stacks 09EV "(6b) intermediate fields of a tame uniformizer-root extension"]
theorem exists_eq_adjoin_root_pow [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} {n : ℕ}
    {hField : Field (RootExtension π n)}
    {hK : Algebra (FractionRing A) (RootExtension π n)}
    (hπ : Irreducible π) (hn : 2 ≤ n)
    (hprime : DVR.Field.PrimeToResidueChar A n)
    (S : @IntermediateField (FractionRing A) (RootExtension π n) _ hField hK) :
    ∃ d : ℕ, d ∣ n ∧
      S = @IntermediateField.adjoin (FractionRing A) _ (RootExtension π n)
        hField hK {root π n ^ (n / d)} := sorry
-- Proof strategy: attach to `S` the ramification index `d` of its integral closure over `A`.
-- Tower multiplicativity and total ramification give `d ∣ n`; tameness rules out defect and
-- inseparable residue contributions.  Compare the valuation of `root^(n/d)` with the value group
-- of `S` to prove it lies in `S`, then compare the finite degrees of `S` and the simple field it
-- generates.  Equality of degrees upgrades the inclusion to the stated intermediate-field equality.

end DVR

section TameCriterion

/-- An unramified field extension after adjoining an `e`th root of a chosen uniformizer.

The witnesses retain the finite separable extension over the fraction field of the explicit
root ring and the embedding of the original fraction-field extension. -/
@[stacks 0EXW "unramified uniformizer-root cover"]
def HasUnramifiedCover
    (A : Type u) [CommRing A] [IsDomain A]
    (L : Type v) [Field L] [Algebra (FractionRing A) L]
    (π : A) (e : ℕ) : Prop :=
  let B := RootRing π e
  let K1 := FractionRing B
  ∃ (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
    (L' : Type (max u v)) (_ : Field L') (_ : Algebra B L') (_ : Algebra K1 L')
    (_ : IsScalarTower B K1 L') (_ : FiniteDimensional K1 L')
    (_ : Algebra.IsSeparable K1 L') (_ : Algebra (FractionRing A) K1)
    (_ : Algebra (FractionRing A) L') (_ : IsScalarTower (FractionRing A) K1 L')
    (_ : Algebra L L') (_ : IsScalarTower (FractionRing A) L L'),
    DVR.Field.IsUnramified B K1 L'

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

/-- Tame ramification is equivalent to admitting an unramified extension after adjoining a
prime-to-residue-characteristic root of a uniformizer, either once or uniformly for all
prime-to-residue-characteristic multiples of one exponent. -/
@[stacks 0EXW "Lemma 15.115.7: tame ramification via uniformizer-root extensions"]
theorem isTamelyRamified_tfae_uniformizerRootCover
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    List.TFAE
      ([ DVR.Field.IsTamelyRamified A (FractionRing A) L
      , ∃ e : ℕ, 1 ≤ e ∧ DVR.Field.PrimeToResidueChar A e ∧
          HasUnramifiedCover A L π e
      , ∃ e0 : ℕ, 1 ≤ e0 ∧ DVR.Field.PrimeToResidueChar A e0 ∧
          ∀ d : ℕ, 1 ≤ d → DVR.Field.PrimeToResidueChar A d →
            HasUnramifiedCover A L π (d * e0)
      ] : List Prop) := sorry
-- Proof strategy: prove the three TFAE links cyclically.  From tameness, take `e0` to be the common
-- prime-to-characteristic ramification index and form a finite separable common overfield with the
-- corresponding uniformizer-root extension; multiplicativity cancels the ramification index, so
-- the upper extension is unramified.  Repeating the construction after a prime-to-characteristic
-- multiple `d` proves the uniform clause.  Specializing that clause at `d = 1` gives a single
-- cover.  Conversely, combine tameness of the uniformizer-root extension with unramifiedness of the
-- cover and descend the branchwise residue/index conditions to recover tameness of `L`.

end TameCriterion

end DVR.UniformizerRoot
