module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Example_87_13_2
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Definition_88_21_1_AdicSquare

/-!
# Complete DVR tests miss rank-one series rings

The complete discrete valuation ring test of Definition 88.21.1 is already
wrong for finite-type morphisms of locally adic* formal algebraic spaces: the
`t`-adic rational-exponent series ring admits no adic map from a complete
discrete valuation ring, so the test is vacuous, while Berkovich-style tests
use complete rank-at-most-one valuation rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open RationalExponentSeries IsLocalRing

noncomputable section

universe u

namespace RationalExponentSeries

/-- The `t`-adic topology on the rational-exponent series ring is pre-adic. -/
instance instIsPreadicRing (κ : Type u) [CommRing κ] :
    TopologicalRing.IsPreadicRing (RationalExponentSeries κ) where
  exists_ideal_isAdic := ⟨Ideal.span {t κ}, isAdic_span_t κ⟩

end RationalExponentSeries

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- There is no adic ring map from the rational-exponent series ring to a
complete discrete valuation ring equipped with its maximal-adic topology. -/
theorem not_isAdicHom_completeDVR {κ R : Type u} [Field κ] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] [TopologicalSpace R]
    [TopologicalRing.IsPreadicRing R] (hR : IsAdic (maximalIdeal R))
    (φ : RationalExponentSeries κ →+* R) : ¬ φ.IsAdicHom :=
  sorry

/-- Remark 88.21.2 (1): if `A` is the `t`-adic completion of `⋃ n, κ[t^{1/n}]`,
then there are no adic morphisms `Spf(R) ⟶ Spf(A)` from a complete discrete
valuation ring `R`. -/
@[stacks 0AQZ]
theorem isEmpty_adicSpfSquare {κ : Type u} [Field κ] {S : Scheme.{u}}
    (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
    {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ AffineFormalAlgebraicSpace.spf (RationalExponentSeries κ) structureHom) :
    IsEmpty (AdicSpfSquare f) :=
  sorry

/-- Remark 88.21.2 (2): consequently every morphism `X ⟶ Spf(A)` satisfies the
complete discrete valuation ring lifting test of Definition 88.21.1 vacuously.
This does not mean the morphism is `RigSurjective`, which requires locally
Noetherian source and target. -/
@[stacks 0AQZ]
theorem dvrTest_vacuous {κ : Type u} [Field κ] {S : Scheme.{u}}
    (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
    {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ AffineFormalAlgebraicSpace.spf (RationalExponentSeries κ) structureHom) :
    ∀ sq : AdicSpfSquare f, Nonempty sq.Extension :=
  sorry

/-- Remark 88.21.2 (3): `A` is a domain and the monomial `t` is nonzero, so `A`
should have a rig-point; the empty space is the unwanted discrete-valuation
vacuous case. -/
@[stacks 0AQZ]
theorem isDomain_and_t_ne_zero (κ : Type u) [Field κ] :
    IsDomain (RationalExponentSeries κ) ∧ t κ ≠ 0 :=
  sorry

/-- The principal ideal `span {t}` has radical equal to the maximal ideal, so
together with the existing `t`-adic completeness it is a Berkovich test ideal
on `A`. -/
theorem radical_span_t_eq_maximalIdeal (κ : Type u) [Field κ] :
    (Ideal.span {t κ}).radical = maximalIdeal (RationalExponentSeries κ) :=
  sorry

/-- Remark 88.21.2 (4): a valuation ring complete with respect to a principal
ideal `J` whose radical is the maximal ideal has rank at most one, so its
value group embeds into `(ℝ, +)`. -/
@[stacks 0AQZ]
theorem isRankLeOne_of_completePrincipal {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] [ValuativeRel R]
    [Valuation.Compatible (valuationRingComap R)]
    [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) [IsAdicComplete J R] (h_prin : J.IsPrincipal) (h_adic : IsAdic J)
    (h_rad : J.radical = maximalIdeal R) : ValuativeRel.IsRankLeOne R :=
  sorry

/-- A rank-at-most-one valuative relation supplies a strictly monotone
embedding of the value group-with-zero into the nonnegative reals. -/
theorem exists_strictMono_emb (R : Type u) [CommRing R] [ValuativeRel R]
    [ValuativeRel.IsRankLeOne R] :
    ∃ emb : ValuativeRel.ValueGroupWithZero R →*₀ NNReal, StrictMono emb :=
  sorry

/-- Remark 88.21.2 (5): Huber's test drops the hypothesis that
`Spec(R ⧸ J)` is a singleton, equivalently that the radical of `J` is the
maximal ideal of the local ring `R`. -/
@[stacks 0AQZ]
theorem unique_primeSpectrum_quotient_iff {R : Type u} [CommRing R] [IsLocalRing R]
    (J : Ideal R) :
    Nonempty (Unique (PrimeSpectrum (R ⧸ J))) ↔ J.radical = maximalIdeal R :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
