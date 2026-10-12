/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Example_87_13_2_FormalSpectrum
public import stacks_project.Chap87.Example_87_13_2_RationalExponentSeries

/-!
# Example 87.13.2

A rank-one valuation ring that is `π`-adically complete for nonzero `π` in the
maximal ideal, with that maximal ideal not finitely generated, has affine
formal spectrum `Spf(A)` whose residue-field stage is a thickening
corresponding to the weak ideal of definition `m`, which is not an ideal of
definition.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite IsLocalRing
open RationalExponentSeries

universe u v

/-- The canonical valuation-ring valuation of `A`, pulled back along
`algebraMap A (FractionRing A)`. -/
abbrev valuationRingComap (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    Valuation A (ValuationRing.ValueGroup A (FractionRing A)) :=
  (ValuationRing.valuation A (FractionRing A)).comap (algebraMap A (FractionRing A))

/-- `valuationRingComap A` is the comap of `ValuationRing.valuation A (FractionRing A)`. -/
theorem valuationRingComap_eq (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    valuationRingComap A =
      (ValuationRing.valuation A (FractionRing A)).comap
        (algebraMap A (FractionRing A)) :=
  sorry

/-- Example 87.13.2 (1): the maximal ideal of a rank-one `π`-adically complete
valuation ring with `π ∈ m` nonzero is a weak ideal of definition. Rank at most
one is taken with respect to `ValuationRing.valuation A (FractionRing A)`. -/
@[stacks 0CB8]
theorem isWeakIdealOfDefinition_maximalIdeal {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (maximalIdeal A) :=
  sorry

/-- Example 87.13.2 (2): in the same situation, the maximal ideal is not an
ideal of definition. -/
@[stacks 0CB8]
theorem not_isIdealOfDefinition_maximalIdeal {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG) :
    ¬ TopologicalRing.Ideal.IsIdealOfDefinition (maximalIdeal A) :=
  sorry

/-- The `p`-adic topology on `𝓞_ℂ_[p]`. -/
instance instTopologicalSpace (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (PadicComplexInt p) :=
  (Ideal.span {(p : PadicComplexInt p)}).adicTopology

/-- The `p`-adic topology is a ring topology. -/
instance instIsTopologicalRing (p : ℕ) [Fact p.Prime] :
    IsTopologicalRing (PadicComplexInt p) :=
  sorry

/-- The ambient topology on `𝓞_ℂ_[p]` is the `p`-adic topology. -/
theorem isAdic_span_p (p : ℕ) [Fact p.Prime] :
    IsAdic (Ideal.span {(p : PadicComplexInt p)}) :=
  sorry

/-- The valuative relation on `𝓞_ℂ_[p]` induced by the `p`-adic valuation. -/
instance instValuativeRel (p : ℕ) [Fact p.Prime] :
    ValuativeRel (PadicComplexInt p) :=
  ValuativeRel.ofValuation <|
    (PadicComplex.valued p).v.comap (algebraMap (PadicComplexInt p) ℂ_[p])

/-- The canonical valuation-ring valuation of `𝓞_ℂ_[p]` is compatible with
the `p`-adic valuative relation. -/
instance instCompatible_valuationRing_comap (p : ℕ) [Fact p.Prime] :
    Valuation.Compatible (valuationRingComap (PadicComplexInt p)) :=
  sorry

/-- `𝓞_ℂ_[p]` has rank at most one; its value group is `ℚ`. -/
instance instIsRankLeOne (p : ℕ) [Fact p.Prime] :
    ValuativeRel.IsRankLeOne (PadicComplexInt p) :=
  sorry

/-- The ring of integers `𝓞_ℂ_[p]` of the `p`-adic complex numbers is
`p`-adically complete. -/
instance instIsAdicComplete_span_p (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (Ideal.span {(p : PadicComplexInt p)}) (PadicComplexInt p) :=
  sorry

/-- `𝓞_ℂ_[p]` is weakly admissible in the `p`-adic topology. -/
instance instIsWeaklyAdmissibleRing_padicComplexInt (p : ℕ) [Fact p.Prime] :
    TopologicalRing.IsWeaklyAdmissibleRing (PadicComplexInt p) :=
  sorry

/-- Example 87.13.2 (3): `A = 𝓞_ℂ_[p]` and `π = p` satisfy the standing
hypotheses that `p` is a nonzero element of the maximal ideal and that this
maximal ideal is not finitely generated. -/
@[stacks 0CB8]
theorem padicComplexInt_example (p : ℕ) [Fact p.Prime] :
    (p : PadicComplexInt p) ∈ maximalIdeal (PadicComplexInt p) ∧
      (p : PadicComplexInt p) ≠ 0 ∧ ¬ (maximalIdeal (PadicComplexInt p)).FG :=
  sorry

/-- Unpacking of `padicComplexInt_example`: `p` lies in the maximal ideal. -/
theorem padicComplexInt_mem_maximalIdeal (p : ℕ) [Fact p.Prime] :
    (p : PadicComplexInt p) ∈ maximalIdeal (PadicComplexInt p) :=
  sorry

/-- Unpacking of `padicComplexInt_example`: `p` is nonzero in `𝓞_ℂ_[p]`. -/
theorem padicComplexInt_ne_zero (p : ℕ) [Fact p.Prime] :
    (p : PadicComplexInt p) ≠ 0 :=
  sorry

/-- Unpacking of `padicComplexInt_example`: the maximal ideal of `𝓞_ℂ_[p]` is
not finitely generated. -/
theorem padicComplexInt_maximalIdeal_not_FG (p : ℕ) [Fact p.Prime] :
    ¬ (maximalIdeal (PadicComplexInt p)).FG :=
  sorry

/-- The series ring is weakly admissible in the `t`-adic topology. -/
instance instIsWeaklyAdmissibleRing_rationalExponentSeries (κ : Type u) [Field κ] :
    TopologicalRing.IsWeaklyAdmissibleRing (RationalExponentSeries κ) :=
  sorry

/-- Example 87.13.2 (4): the rational-exponent series ring with `π = t`
satisfies the standing hypotheses that `t` is a nonzero element of the maximal
ideal and that this maximal ideal is not finitely generated. -/
@[stacks 0CB8]
theorem rationalExponentSeries_example (κ : Type u) [Field κ] :
    t κ ∈ maximalIdeal (RationalExponentSeries κ) ∧
      t κ ≠ 0 ∧ ¬ (maximalIdeal (RationalExponentSeries κ)).FG :=
  sorry

/-- Example 87.13.2 (5): `X = Spf(A)` is an affine formal algebraic space: the
diagram of stages `Spec(A ⧸ I)` is directed, each stage is affine, transition
maps are thickenings, and `spf A structureHom` is the Yoneda colimit of that
diagram. -/
@[stacks 0CB8]
theorem isAffineFormalAlgebraicSpace_spf {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {π : A} (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) :
    IsDirectedAffineYonedaColimit (thickenings A structureHom)
      (spf A structureHom) :=
  sorry

/-- A site realization of the weak-ideal affine stages `Spec(A ⧸ I)` of
`thickenings A structureHom`, together with the coequalizer size condition,
yields an affine formal algebraic space on the corresponding sheaf. -/
theorem isAffineFormalAlgebraicSpace_of_stageRealization {A : Type u}
    [CommRing A] [TopologicalSpace A] {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (hD_obj : ∀ I : WeakIdealOfDefinition A,
      (𝒮.bigAffineToScheme S).obj (D.obj I) ≅ (stage A structureHom I).left)
    (hD_map : ∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
      (𝒮.bigAffineToScheme S).map (D.map f) ≫ (hD_obj J).hom =
        (hD_obj I).hom ≫ ((thickenings A structureHom).map f).left)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X]
    (hX : (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
          IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
        ∃ c : Cocone
          (D ⋙ 𝒮.bigAffineInclusion S ⋙
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor),
          Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)) :
    IsAffineFormalAlgebraicSpace X :=
  sorry

/-- Example 87.13.2 (6): `Spec(κ) ⟶ Spf(A)` is the Yoneda cocone leg of `spf`
at the weak ideal of definition `m` from (1), hence the thickening
corresponding to `m`. -/
@[stacks 0CB8]
theorem specResidue_isThickening {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {π : A} (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) :
    specResidue A structureHom
          (isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG) =
        colimit.ι (thickenings A structureHom ⋙ yoneda)
          (WeakIdealOfDefinition.of (maximalIdeal A)
            (isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG)) ∧
      (stage A structureHom
          (WeakIdealOfDefinition.of (maximalIdeal A)
            (isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG))).left =
        Spec (.of (ResidueField A)) :=
  sorry

/-- Outgoing stage maps from the residue-field thickening are scheme
thickenings. -/
theorem specResidue_map_isThickening {A : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible (valuationRingComap A)] [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {π : A} (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    {J : WeakIdealOfDefinition A}
    (f : WeakIdealOfDefinition.of (maximalIdeal A)
        (isWeakIdealOfDefinition_maximalIdeal hπ hπ0 h_adic hFG) ⟶ J) :
    IsThickening ((thickenings A structureHom).map f).left :=
  sorry
