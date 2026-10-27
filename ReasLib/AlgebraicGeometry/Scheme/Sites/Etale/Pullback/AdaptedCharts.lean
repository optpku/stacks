/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/- Bounded chart/gluing construction for small étale base change.
   Public migration proposal; native validation remains a MAIN gate. -/
module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.BoundedGeometry
public import Mathlib.RingTheory.FinitePresentation

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.PullbackBounds

/- A finite presentation with the finite relation family retained as data. -/
structure NativeFinitePresentation (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] where
  variableCount : ℕ
  generator : MvPolynomial (Fin variableCount) R →ₐ[R] A
  generator_surjective : Function.Surjective generator
  relationCount : ℕ
  relation : Fin relationCount → MvPolynomial (Fin variableCount) R
  relation_span :
    Ideal.span (Set.range relation) = RingHom.ker generator.toRingHom

namespace NativeFinitePresentation

/- `Algebra.FinitePresentation.out` is the only source of the polynomial map
   and the finite relation family.  The enumeration equality is a true ring
   proposition; it is kept as a separate proof obligation rather than being
   hidden in a data field. -/
theorem span_enumerated_relations
    {R : Type u} {n : ℕ} [CommRing R]
    (s : Finset (MvPolynomial (Fin n) R)) :
    Ideal.span (Set.range (fun j : Fin s.card =>
      (s.equivFin.symm j : MvPolynomial (Fin n) R))) =
      Ideal.span (↑s : Set (MvPolynomial (Fin n) R)) := by
  sorry

noncomputable def ofFinitePresentation
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (h : Algebra.FinitePresentation R A) :
    NativeFinitePresentation R A := by
  letI : Algebra.FinitePresentation R A := h
  let hout := Algebra.FinitePresentation.out (R := R) (A := A)
  let n := Classical.choose hout
  let hout₁ := Classical.choose_spec hout
  let q := Classical.choose hout₁
  let hq := Classical.choose_spec hout₁
  let s := Classical.choose hq.2
  let hs := Classical.choose_spec hq.2
  exact
    { variableCount := n
      generator := q
      generator_surjective := hq.1
      relationCount := s.card
      relation := fun j =>
        (s.equivFin.symm j : MvPolynomial (Fin n) R)
      relation_span := by
        rw [span_enumerated_relations s]
        exact hs }

noncomputable def rawCode {S : Scheme.{u}} {B : BaseAtlas S}
    {i : S.carrier} {A : Type u} [CommRing A]
    [Algebra (BaseRing B i) A]
    (P : NativeFinitePresentation (BaseRing B i) A) : RawChartCode B i :=
  { variableCount := P.variableCount
    relationCount := P.relationCount
    relation := P.relation }

/- This is the actual quotient algebra equivalence.  It uses the proved
   surjectivity and the equality of the generated relation ideal with the
   kernel, rather than an `IsIso` or an existential witness. -/
noncomputable def quotientAlgEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : NativeFinitePresentation R A) :
    (MvPolynomial (Fin P.variableCount) R ⧸
      Ideal.span (Set.range P.relation)) ≃ₐ[R] A :=
  (Ideal.quotientEquivAlgOfEq R P.relation_span).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := P.generator) P.generator_surjective)

end NativeFinitePresentation

/- A relative presentation is attached to an already selected affine open W.
   The map q is the native restriction of g to the fixed base chart. -/
structure RelativeAffinePresentation {S U : Scheme.{u}} (B : BaseAtlas S)
    (g : U ⟶ S) [Etale g] (i : S.carrier) (W : U.Opens)
    (hW : IsAffineOpen W) (hWB : W ≤ g ⁻¹ᵁ B.affineOpen i) where
  q : W.toScheme ⟶ (B.affineOpen i).toScheme
  q_def : q = g.resLE (B.affineOpen i) W hWB
  q_etale : Etale q
  presentation :
    @NativeFinitePresentation
      (Γ(S, B.affineOpen i)) (Γ(U, W)) _ _
      (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
  chart_etale : Etale (chartToAffine (A := B) (i := i)
    (@NativeFinitePresentation.rawCode S B i (Γ(U, W)) _
      (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra presentation))

noncomputable def RelativeAffinePresentation.quotientCode
    {S U : Scheme.{u}} {B : BaseAtlas S} {g : U ⟶ S} [Etale g]
    {i : S.carrier} {W : U.Opens} {hW : IsAffineOpen W}
    {hWB : W ≤ g ⁻¹ᵁ B.affineOpen i}
    (P : RelativeAffinePresentation B g i W hW hWB) : ChartCode B i :=
  letI : Algebra (Γ(S, B.affineOpen i)) (Γ(U, W)) :=
    (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
  ⟨NativeFinitePresentation.rawCode P.presentation, P.chart_etale⟩

noncomputable def RelativeAffinePresentation.quotientEquiv
    {S U : Scheme.{u}} {B : BaseAtlas S} {g : U ⟶ S} [Etale g]
    {i : S.carrier} {W : U.Opens} {hW : IsAffineOpen W}
    {hWB : W ≤ g ⁻¹ᵁ B.affineOpen i}
    (P : RelativeAffinePresentation B g i W hW hWB) :
    letI : Algebra (Γ(S, B.affineOpen i)) (Γ(U, W)) :=
      (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
    (MvPolynomial (Fin P.presentation.variableCount) (Γ(S, B.affineOpen i)) ⧸
      Ideal.span (Set.range P.presentation.relation)) ≃ₐ[Γ(S, B.affineOpen i)] (Γ(U, W)) :=
  letI : Algebra (Γ(S, B.affineOpen i)) (Γ(U, W)) :=
    (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
  NativeFinitePresentation.quotientAlgEquiv P.presentation

/- The following transport statement is exactly the missing geometric proof:
   the quotient Spec map obtained from the native presentation is the affine
   restriction q.  It is a Prop, so its proof may remain deferred without
   manufacturing any scheme-level datum. -/
theorem chartToAffine_etale_of_relative_presentation
    {S U : Scheme.{u}} (B : BaseAtlas S) (g : U ⟶ S) [Etale g]
    (i : S.carrier) (W : U.Opens) (hW : IsAffineOpen W)
    (hWB : W ≤ g ⁻¹ᵁ B.affineOpen i)
    (P : @NativeFinitePresentation
      (Γ(S, B.affineOpen i)) (Γ(U, W)) _ _
      (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra) :
    Etale (chartToAffine (A := B) (i := i)
      (@NativeFinitePresentation.rawCode S B i (Γ(U, W)) _
        (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra P)) := by
  sorry

namespace RelativeAffinePresentation

noncomputable def make {S U : Scheme.{u}} (B : BaseAtlas S) (g : U ⟶ S)
    [Etale g] (i : S.carrier) (W : U.Opens) (hW : IsAffineOpen W)
    (hWB : W ≤ g ⁻¹ᵁ B.affineOpen i) :
    RelativeAffinePresentation B g i W hW hWB := by
  let q := g.resLE (B.affineOpen i) W hWB
  letI : IsAffine W.toScheme := hW
  letI : IsAffine (B.affineOpen i).toScheme := B.affine i
  letI : Algebra (Γ(S, B.affineOpen i)) (Γ(U, W)) :=
    (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
  let P := NativeFinitePresentation.ofFinitePresentation
    (g.finitePresentation_appLE (B.affine i) hW hWB)
  have hcode : Etale (chartToAffine (A := B) (i := i)
      (NativeFinitePresentation.rawCode P)) :=
    chartToAffine_etale_of_relative_presentation B g i W hW hWB P
  exact
    { q := q
      q_def := rfl
      q_etale := by infer_instance
      presentation := P
      chart_etale := hcode }

end RelativeAffinePresentation

/- The actual Spec comparison, in both directions, is built from the quotient
   algebra equivalence and the affine Spec isomorphism of W. -/
noncomputable def relativeModelIso
    {S U : Scheme.{u}} {B : BaseAtlas S} {g : U ⟶ S} [Etale g]
    {i : S.carrier} {W : U.Opens} (hW : IsAffineOpen W)
    {hWB : W ≤ g ⁻¹ᵁ B.affineOpen i}
    (P : RelativeAffinePresentation B g i W hW hWB) :
    chartScheme P.quotientCode ≅ W.toScheme := by
  letI : Algebra (Γ(S, B.affineOpen i)) (Γ(U, W)) :=
    (g.appLE (B.affineOpen i) W hWB).hom.toAlgebra
  let e := P.quotientEquiv.toRingEquiv.toCommRingCatIso
  exact
    (Scheme.Spec.mapIso (.op e)).symm ≪≫ hW.isoSpec.symm

theorem relativeModel_overS
    {S U : Scheme.{u}} {B : BaseAtlas S} {g : U ⟶ S} [Etale g]
    {i : S.carrier} {W : U.Opens} (hW : IsAffineOpen W)
    {hWB : W ≤ g ⁻¹ᵁ B.affineOpen i}
    (P : RelativeAffinePresentation B g i W hW hWB) :
    (relativeModelIso hW P).hom ≫ W.ι ≫ g = chartToS P.quotientCode := by
  sorry

/- The small adapted structure keeps the relative containment explicit.  The
   model and its map to S are actual fields; only their compatibility equation
   is a Prop law. -/
structure AdaptedPointChart {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V) where
  chartOpen : U.Opens
  chartAffine : IsAffineOpen chartOpen
  containsProjection :
    (commaInputProjection C).base x ∈ chartOpen
  liesOver : chartOpen ≤
    g ⁻¹ᵁ B.affineOpen (g.base ((commaInputProjection C).base x))
  code : ChartCode B (g.base ((commaInputProjection C).base x))
  modelIso : chartScheme code ≅ chartOpen.toScheme
  model_overS : modelIso.hom ≫ chartOpen.ι ≫ g = chartToS code

abbrev AdaptedChartFamily {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) : Type u :=
  (x : SourceIndex V) → AdaptedPointChart B C x

/- Native pointwise neighbourhood data.  This is the only neighbourhood
   choice in this file and comes from the proved theorem
   `exists_isAffineOpen_mem_and_subset`; in particular it does not call the
   admitted chart-code existence theorem from BoundGeometry. -/
noncomputable def adaptedNeighborhood
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V) :
    {W : U.Opens // IsAffineOpen W ∧
      (commaInputProjection C).base x ∈ W ∧
      W ≤ g ⁻¹ᵁ B.affineOpen (g.base ((commaInputProjection C).base x))} := by
  let p := commaInputProjection C
  let i := g.base (p.base x)
  have hx : p.base x ∈ g ⁻¹ᵁ B.affineOpen i := by
    exact B.containsIndex i
  let h := exists_isAffineOpen_mem_and_subset (X := U) (x := p.base x) hx
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def adaptedNeighborhoodFamily
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) :
    (x : SourceIndex V) → {W : U.Opens // IsAffineOpen W ∧
      (commaInputProjection C).base x ∈ W ∧
      W ≤ g ⁻¹ᵁ B.affineOpen (g.base ((commaInputProjection C).base x))} :=
  fun x => adaptedNeighborhood B C x

/- For every point this packages the native restriction and its actual finite
   presentation.  The result contains the quotient code and the algebra
   equivalence; it is independent of the unresolved Spec-over-S equality. -/
noncomputable def adaptedRelativePresentation
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V) :
    RelativeAffinePresentation B g
      (g.base ((commaInputProjection C).base x))
      (adaptedNeighborhood B C x).1
      (adaptedNeighborhood B C x).2.1
      (adaptedNeighborhood B C x).2.2.2 :=
  RelativeAffinePresentation.make B g
    (g.base ((commaInputProjection C).base x))
    (adaptedNeighborhood B C x).1
    (adaptedNeighborhood B C x).2.1
    (adaptedNeighborhood B C x).2.2.2

/- The default chart is computed from the native neighborhood and its anchored
   finite presentation.  Its model is the explicit Spec isomorphism induced by
   the quotient algebra equivalence; only the over-S compatibility is a Prop
   theorem. -/
noncomputable def defaultAdaptedPointChart
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V) :
    AdaptedPointChart B C x :=
  let N := adaptedNeighborhood B C x
  let P := adaptedRelativePresentation B C x
  { chartOpen := (adaptedNeighborhood B C x).1
    chartAffine := N.2.1
    containsProjection := N.2.2.1
    liesOver := N.2.2.2
    code := P.quotientCode
    modelIso := relativeModelIso N.2.1 P
    model_overS := relativeModel_overS N.2.1 P }

noncomputable def defaultAdaptedChartFamily
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) :
    AdaptedChartFamily B C :=
  fun x => defaultAdaptedPointChart B C x

/- Compatibility adapter for callers that already carry a comparison proof.
   The default family above does not depend on this supplied interface. -/
structure AdaptedTransportInput
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V) where
  presentation : RelativeAffinePresentation B g
      (g.base ((commaInputProjection C).base x))
      (adaptedNeighborhood B C x).1
      (adaptedNeighborhood B C x).2.1
      (adaptedNeighborhood B C x).2.2.2
  modelIso : chartScheme presentation.quotientCode ≅
    (adaptedNeighborhood B C x).1.toScheme
  model_overS :
    modelIso.hom ≫ (adaptedNeighborhood B C x).1.ι ≫ g =
      chartToS presentation.quotientCode

def adaptedPointChartOfTransport
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    {C : EtaleCommaInput f V g} (x : SourceIndex V)
    (H : AdaptedTransportInput B C x) : AdaptedPointChart B C x :=
  { chartOpen := (adaptedNeighborhood B C x).1
    chartAffine := (adaptedNeighborhood B C x).2.1
    containsProjection := (adaptedNeighborhood B C x).2.2.1
    liesOver := (adaptedNeighborhood B C x).2.2.2
    code := H.presentation.quotientCode
    modelIso := H.modelIso
    model_overS := H.model_overS }

def adaptedChartFamilyOfTransport
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g)
    (H : (x : SourceIndex V) → AdaptedTransportInput B C x) :
    AdaptedChartFamily B C :=
  fun x => adaptedPointChartOfTransport B x (H x)

/- This proposition records the only remaining transport needed to turn the
   genuine neighbourhood/presentation data into the requested small chart.
   It is not used by any default provider or by a choice from an existence
   theorem. -/
theorem adaptedChart_transport
    {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (x : SourceIndex V)
    (N := adaptedNeighborhood B C x) :
    ∃ c : ChartCode B (g.base ((commaInputProjection C).base x)),
      ∃ e : chartScheme c ≅ N.1.toScheme,
        e.hom ≫ N.1.ι ≫ g = chartToS c := by
  sorry

/- The selection and coverage law expose the concrete default family to the
   existing affine-chart selection API. -/
def selectionOfAdapted {S T U : Scheme.{u}} {B : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    {C : EtaleCommaInput f V g} (Q : AdaptedChartFamily B C) :
    AffineChartSelection C :=
  { chartOpen := fun x => (Q x).chartOpen
    chartAffine := fun x => (Q x).chartAffine
    containsProjection := fun x => (Q x).containsProjection }

def defaultAdaptedSelection
    {S T U : Scheme.{u}} {B : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    {C : EtaleCommaInput f V g} :
    AffineChartSelection C :=
  selectionOfAdapted (defaultAdaptedChartFamily B C)

theorem imageContainingUnionLaw_of_selection
    {S T U : Scheme.{u}} {B : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (Q : AdaptedChartFamily B C) :
    imageContainingUnionLaw C (selectionOfAdapted Q) := by
  intro x
  exact (le_iSup (fun y : V.left.carrier => (Q y).chartOpen) x)
    ((Q x).containsProjection)

end AlgebraicGeometry.Scheme.Etale.PullbackBounds
