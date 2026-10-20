/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.RationalExponentSeries
public import ReasLib.RingTheory.LocalRing.PrimeSpectrum
import StacksCheckRecall

/-!
# Complete DVR tests miss rank-one series rings

The `t`-adic completion of `⋃ n ≥ 1, κ[t^(1/n)]` is realized by the ring of
nonnegative rational-exponent series with finite support in each bounded
interval. Its sheaf formal spectrum admits no adic map from the formal
spectrum of a complete discrete valuation ring. Thus the DVR lifting test of
Definition 88.21.1 is vacuous for every morphism into it, including one with
empty source. Since the series ring is a domain and `t ≠ 0`, the intended
notion should still detect a rig-point. This warns against extending the
DVR test beyond the locally Noetherian setting, even for finite-type
morphisms of locally adic* formal algebraic spaces.

Berkovich's broader tests use valuation rings complete for a principal
ideal whose radical is maximal; their value groups embed into the real
numbers. Huber further drops the requirement that the quotient spectrum
be a singleton. The checks below retain these two alternatives.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open IsLocalRing

universe u

/- Remark 88.21.2: the sheaf formal spectrum of the completed polynomial union
has no adic complete-DVR test morphisms. -/
@[stacks 0AQZ] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.isEmpty_adicSpfSquare :
    ∀ {κ : Type u} [Field κ] {S : Scheme.{u}}
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
      {X : (Over S)ᵒᵖ ⥤ Type u}
      (f : X ⟶ (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf
        (RationalExponentSeries κ) structureHom).obj),
      IsEmpty (AdicSpfSquare f))

#check (RationalExponentSeries.instIsPreadicRing :
  ∀ (κ : Type u) [CommRing κ],
    TopologicalRing.IsPreadicRing (RationalExponentSeries κ))

#check (RationalExponentSeries.not_isAdicHom_completeDVR :
  ∀ {κ R : Type u} [Field κ] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] [TopologicalSpace R]
    [TopologicalRing.IsPreadicRing R],
    IsAdic (maximalIdeal R) →
    ∀ (φ : RationalExponentSeries κ →+* R), ¬ φ.IsAdicHom)

#check (AlgebraicGeometry.FormalAlgebraicSpace.dvrTest_vacuous :
  ∀ {κ : Type u} [Field κ] {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of (RationalExponentSeries κ)) ⟶ S)
    {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf
      (RationalExponentSeries κ) structureHom).obj),
    ∀ sq : AdicSpfSquare f, Nonempty sq.Extension)

#check (RationalExponentSeries.instIsDomain :
  ∀ (κ : Type u) [Field κ], IsDomain (RationalExponentSeries κ))

#check (RationalExponentSeries.t_ne_zero :
  ∀ (κ : Type u) [Field κ], RationalExponentSeries.t κ ≠ 0)

#check (RationalExponentSeries.radical_span_t_eq_maximalIdeal :
  ∀ (κ : Type u) [Field κ],
    (Ideal.span {RationalExponentSeries.t κ}).radical =
      maximalIdeal (RationalExponentSeries κ))

#check (ValuationRing.Adic.exists_strictMono_emb_of_completePrincipal :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [ValuativeRel R]
    [Valuation.Compatible (ValuationRing.Adic.valuationRingComap R)]
    [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) [IsAdicComplete J R],
    J.IsPrincipal → IsAdic J → J.radical = maximalIdeal R →
    ∃ emb : ValuativeRel.ValueGroupWithZero R →*₀ NNReal, StrictMono emb)

#check (ValuativeRel.IsRankLeOne.nonempty :
  ∀ {R : Type u} [CommRing R] [ValuativeRel R] [ValuativeRel.IsRankLeOne R],
    Nonempty (ValuativeRel.RankLeOneStruct R))

#check (IsLocalRing.unique_primeSpectrum_quotient_iff :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (J : Ideal R),
    Nonempty (Unique (PrimeSpectrum (R ⧸ J))) ↔ J.radical = maximalIdeal R)
