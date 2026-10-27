/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/- Bounded chart/gluing construction for small étale base change.
   Public migration proposal; native validation remains a MAIN gate. -/
module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.BoundedGeometry

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.PullbackBounds.AdaptedGluing

/-- Input from a chart encoder. The index and the target opens are fixed before
forming their union. `overS` anchors each supplied model to its coded base map. -/
structure Family {S T U : Scheme.{u}} (B : BaseAtlas S)
    {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) : Type u where
  W : SourceIndex V → U.Opens
  affine : ∀ x, IsAffineOpen (W x)
  baseIndex : SourceIndex V → S.carrier
  code : ∀ x, ChartCode B (baseIndex x)
  theta : ∀ x, chartScheme (code x) ≅ (W x).toScheme
  overS : ∀ x, (theta x).hom ≫ (W x).ι ≫ g = chartToS (code x)
  containsProjection : ∀ x, (commaInputProjection C).base x ∈ W x

variable {S T U : Scheme.{u}} {B : BaseAtlas S}
variable {f : T ⟶ S} {V : T.Etale} {g : U ⟶ S} [Etale g]
variable {C : EtaleCommaInput f V g}

abbrev X (Q : Family B C) (x : SourceIndex V) : Scheme.{u} :=
  chartScheme (Q.code x)

def selection (Q : Family B C) : AffineChartSelection C where
  chartOpen := Q.W
  chartAffine := Q.affine
  containsProjection := Q.containsProjection

theorem unionLaw (Q : Family B C) : imageContainingUnionLaw C (selection Q) := by
  intro x
  exact (le_iSup Q.W x) (Q.containsProjection x)

def chartMap (Q : Family B C) (x : SourceIndex V) : X Q x ⟶ U :=
  (Q.theta x).hom ≫ (Q.W x).ι

instance chartMap_openImmersion (Q : Family B C) (x : SourceIndex V) :
    IsOpenImmersion (chartMap Q x) := by
  dsimp [chartMap]
  infer_instance

def overlap (Q : Family B C) (x y : SourceIndex V) : (X Q x).Opens :=
  chartMap Q x ⁻¹ᵁ Q.W y

def overlapMap (Q : Family B C) (x y : SourceIndex V) :
    (overlap Q x y).toScheme ⟶ U :=
  (overlap Q x y).ι ≫ chartMap Q x

instance overlapMap_openImmersion (Q : Family B C) (x y : SourceIndex V) :
    IsOpenImmersion (overlapMap Q x y) := by
  dsimp [overlapMap]
  infer_instance

/-- Proof debt: restriction of an open immersion to a preimage has precisely
its range intersected with that open. The supplied theta is surjective. -/
theorem overlap_range (Q : Family B C) (x y : SourceIndex V) :
    Set.range (overlapMap Q x y).base =
      (Q.W x : Set U.carrier) ∩ (Q.W y : Set U.carrier) := by
  sorry

def transition (Q : Family B C) (x y : SourceIndex V) :
    (overlap Q x y).toScheme ≅ (overlap Q y x).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (X := (overlap Q x y).toScheme)
    (Y := (overlap Q y x).toScheme)
    (Z := U) (overlapMap Q x y) (overlapMap Q y x)
    (by rw [overlap_range, overlap_range, Set.inter_comm])

@[reassoc (attr := simp)]
theorem transition_fac (Q : Family B C) (x y : SourceIndex V) :
    (transition Q x y).hom ≫ overlapMap Q y x = overlapMap Q x y :=
  IsOpenImmersion.isoOfRangeEq_hom_fac
    (X := (overlap Q x y).toScheme)
    (Y := (overlap Q y x).toScheme)
    (Z := U) (overlapMap Q x y) (overlapMap Q y x) _

theorem overlap_self (Q : Family B C) (x : SourceIndex V) :
    overlap Q x x = ⊤ := by
  simp only [overlap, chartMap, Scheme.Hom.comp_preimage,
    Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

/-- This uses the native top-open inverse, not an admitted IsIso. -/
theorem self_inclusion_isIso (Q : Family B C) (x : SourceIndex V) :
    IsIso ((overlap Q x x).ι) := by
  rw [overlap_self]
  change IsIso ((⊤ : (X Q x).Opens).ι)
  exact (inferInstance : IsIso (X Q x).topIso.hom)

theorem transition_self (Q : Family B C) (x : SourceIndex V) :
    (transition Q x x).hom = 𝟙 _ := by
  apply (cancel_mono (overlapMap Q x x)).1
  simp only [transition_fac, Category.id_comp]

abbrev Triple (Q : Family B C) (x y z : SourceIndex V) : Scheme.{u} :=
  pullback ((overlap Q x y).ι) ((overlap Q x z).ι)

def tripleToChart (Q : Family B C) (x y z : SourceIndex V) :
    Triple Q x y z ⟶ X Q y :=
  pullback.fst ((overlap Q x y).ι) ((overlap Q x z).ι) ≫
    (transition Q x y).hom ≫ (overlap Q y x).ι

/-- Proof debt: both projections have the same map to U; the z projection
lands in W_z. Transition_fac then gives membership in the y,z overlap. -/
theorem triple_range (Q : Family B C) (x y z : SourceIndex V) :
    Set.range (tripleToChart Q x y z).base ⊆
      Set.range ((overlap Q y z).ι).base := by
  sorry

def tripleFactor (Q : Family B C) (x y z : SourceIndex V) :
    Triple Q x y z ⟶ (overlap Q y z).toScheme :=
  IsOpenImmersion.lift (overlap Q y z).ι (tripleToChart Q x y z)
    (triple_range Q x y z)

@[reassoc (attr := simp)]
theorem tripleFactor_fac (Q : Family B C) (x y z : SourceIndex V) :
    tripleFactor Q x y z ≫ (overlap Q y z).ι = tripleToChart Q x y z :=
  IsOpenImmersion.lift_fac _ _ _

def tripleTurn (Q : Family B C) (x y z : SourceIndex V) :
    Triple Q x y z ⟶ Triple Q y z x :=
  pullback.lift (tripleFactor Q x y z)
    (pullback.fst ((overlap Q x y).ι) ((overlap Q x z).ι) ≫
      (transition Q x y).hom)
    (tripleFactor_fac Q x y z)

theorem tripleTurn_snd (Q : Family B C) (x y z : SourceIndex V) :
    tripleTurn Q x y z ≫
      pullback.snd ((overlap Q y z).ι) ((overlap Q y x).ι) =
    pullback.fst ((overlap Q x y).ι) ((overlap Q x z).ι) ≫
      (transition Q x y).hom := by
  simp only [tripleTurn, pullback.lift_snd]

/-- Proof debt: all three rotations preserve the scheme morphism to U.
Cancel the open immersions and use pullback.hom_ext for the two projections. -/
theorem tripleTurn_cocycle (Q : Family B C) (x y z : SourceIndex V) :
    tripleTurn Q x y z ≫ tripleTurn Q y z x ≫ tripleTurn Q z x y = 𝟙 _ := by
  sorry

/-- Proof debt: transition_fac is equality of scheme morphisms to U;
composing with g and substituting Q.overS gives this equality over S. -/
theorem charts_overS (Q : Family B C) (x y : SourceIndex V) :
    (overlap Q x y).ι ≫ chartToS (Q.code x) =
      ((transition Q x y).hom ≫ (overlap Q y x).ι) ≫ chartToS (Q.code y) := by
  sorry

/-- The exact fixed point index, coded charts, preimage overlaps and lift data
are passed to the frozen bounded-atlas constructor. -/
def boundedAtlas (Q : Family B C) : BoundedAtlas B f V where
  chart x := ⟨Q.baseIndex x, Q.code x⟩
  openOverlap := overlap Q
  transition := transition Q
  selfOpenIso := self_inclusion_isIso Q
  transition_id := transition_self Q
  tripleFactor := tripleFactor Q
  tripleFactor_compat := tripleFactor_fac Q
  t_fac := tripleTurn_snd Q
  cocycle := tripleTurn_cocycle Q
  chart_over_S := charts_overS Q

/-- Native Scheme.GlueData evaluation of the explicit bounded atlas. -/
def nativeSchemeGlueData (Q : Family B C) : Scheme.GlueData.{u} :=
  (boundedAtlas Q).schemeGlueData

abbrev Union (Q : Family B C) : Scheme.{u} :=
  (imageContainingUnion C (selection Q)).toScheme

def unionCover (Q : Family B C) : (Union Q).OpenCover :=
  Scheme.Opens.iSupOpenCover Q.W

def toUnionChart (Q : Family B C) (x : SourceIndex V) : X Q x ⟶ Union Q :=
  (Q.theta x).hom ≫ U.homOfLE (le_iSup Q.W x)

/-- Proof debt: use overlapPullbackIso, transition_fac and cancellation by the
union inclusion. This is compatibility on the actual native gluing cover. -/
theorem forward_compatible (Q : Family B C) (x y : SourceIndex V) :
    pullback.fst ((boundedAtlas Q).schemeGlueData.ι x)
        ((boundedAtlas Q).schemeGlueData.ι y) ≫ toUnionChart Q x =
      pullback.snd ((boundedAtlas Q).schemeGlueData.ι x)
        ((boundedAtlas Q).schemeGlueData.ι y) ≫ toUnionChart Q y := by
  sorry

def forward (Q : Family B C) : (boundedAtlas Q).gluedScheme ⟶ Union Q :=
  (boundedAtlas Q).schemeGlueData.openCover.glueMorphisms (toUnionChart Q)
    (forward_compatible Q)

@[simp]
theorem forward_chart (Q : Family B C) (x : SourceIndex V) :
    (boundedAtlas Q).schemeGlueData.ι x ≫ forward Q = toUnionChart Q x :=
  (boundedAtlas Q).schemeGlueData.openCover.ι_glueMorphisms _ _ x

def fromUnionChart (Q : Family B C) (x : SourceIndex V) :
    (Q.W x).toScheme ⟶ (boundedAtlas Q).gluedScheme :=
  (Q.theta x).inv ≫ (boundedAtlas Q).schemeGlueData.ι x

/-- Proof debt: on W_x intersect W_y, transition_fac identifies theta.inv;
the native scheme glue_condition identifies their chart inclusions. -/
theorem inverse_compatible (Q : Family B C) (x y : SourceIndex V) :
    pullback.fst ((unionCover Q).f x) ((unionCover Q).f y) ≫ fromUnionChart Q x =
      pullback.snd ((unionCover Q).f x) ((unionCover Q).f y) ≫ fromUnionChart Q y := by
  sorry

/-- Actual inverse data, obtained by gluing theta.inv on iSupOpenCover. -/
def inverse (Q : Family B C) : Union Q ⟶ (boundedAtlas Q).gluedScheme :=
  (unionCover Q).glueMorphisms (fromUnionChart Q) (inverse_compatible Q)

@[reassoc (attr := simp)]
theorem inverse_chart (Q : Family B C) (x : SourceIndex V) :
    U.homOfLE (le_iSup Q.W x) ≫ inverse Q = fromUnionChart Q x :=
  (unionCover Q).ι_glueMorphisms _ _ x

set_option backward.isDefEq.respectTransparency false in
theorem forward_inverse (Q : Family B C) : forward Q ≫ inverse Q = 𝟙 _ := by
  apply (boundedAtlas Q).schemeGlueData.openCover.hom_ext
  intro (x : SourceIndex V)
  change (boundedAtlas Q).schemeGlueData.ι x ≫ (forward Q ≫ inverse Q) =
    (boundedAtlas Q).schemeGlueData.ι x ≫ 𝟙 _
  calc
    (boundedAtlas Q).schemeGlueData.ι x ≫ (forward Q ≫ inverse Q) =
        ((boundedAtlas Q).schemeGlueData.ι x ≫ forward Q) ≫ inverse Q := by
      simp only [Category.assoc]
    _ = toUnionChart Q x ≫ inverse Q := by
      exact congrArg (fun k => k ≫ inverse Q) (forward_chart Q x)
    _ = (Q.theta x).hom ≫
        (U.homOfLE (le_iSup Q.W x) ≫ inverse Q) := by
      simp only [toUnionChart, Category.assoc]
    _ = (Q.theta x).hom ≫ fromUnionChart Q x := by
      exact congrArg (fun k => (Q.theta x).hom ≫ k) (inverse_chart Q x)
    _ = (boundedAtlas Q).schemeGlueData.ι x := by
      change (Q.theta x).hom ≫
          ((Q.theta x).inv ≫ (boundedAtlas Q).schemeGlueData.ι x) =
        (boundedAtlas Q).schemeGlueData.ι x
      simp
    _ = (boundedAtlas Q).schemeGlueData.ι x ≫ 𝟙 _ := by simp

set_option backward.isDefEq.respectTransparency false in
theorem inverse_forward (Q : Family B C) : inverse Q ≫ forward Q = 𝟙 _ := by
  apply (unionCover Q).hom_ext
  intro (x : SourceIndex V)
  change U.homOfLE (le_iSup Q.W x) ≫ (inverse Q ≫ forward Q) =
    U.homOfLE (le_iSup Q.W x) ≫ 𝟙 _
  calc
    U.homOfLE (le_iSup Q.W x) ≫ (inverse Q ≫ forward Q) =
        (U.homOfLE (le_iSup Q.W x) ≫ inverse Q) ≫ forward Q := by
      simp only [Category.assoc]
    _ = fromUnionChart Q x ≫ forward Q := by
      exact congrArg (fun k => k ≫ forward Q) (inverse_chart Q x)
    _ = (Q.theta x).inv ≫
        ((boundedAtlas Q).schemeGlueData.ι x ≫ forward Q) := by
      simp only [fromUnionChart, Category.assoc]
    _ = (Q.theta x).inv ≫ toUnionChart Q x := by
      exact congrArg (fun k => (Q.theta x).inv ≫ k) (forward_chart Q x)
    _ = U.homOfLE (le_iSup Q.W x) := by
      rw [toUnionChart, Iso.inv_hom_id_assoc]
    _ = U.homOfLE (le_iSup Q.W x) ≫ 𝟙 _ := by simp

/-- Both morphisms were constructed before proving their inverse laws. -/
def comparison (Q : Family B C) : (boundedAtlas Q).gluedScheme ≅ Union Q where
  hom := forward Q
  inv := inverse Q
  hom_inv_id := forward_inverse Q
  inv_hom_id := inverse_forward Q

set_option backward.isDefEq.respectTransparency false in
theorem comparison_overS (Q : Family B C) :
    (comparison Q).hom ≫ (imageContainingUnionMap C (selection Q) ≫ g) =
      (boundedAtlas Q).gluedToS (coverCompat_of_chart_over_S (boundedAtlas Q)) := by
  apply (boundedAtlas Q).schemeGlueData.openCover.hom_ext
  intro (x : SourceIndex V)
  change (boundedAtlas Q).schemeGlueData.ι x ≫
      (forward Q ≫ (imageContainingUnionMap C (selection Q) ≫ g)) = _
  rw [← Category.assoc, forward_chart Q x]
  calc
    toUnionChart Q x ≫ (imageContainingUnionMap C (selection Q) ≫ g) =
        chartToS (Q.code x) := by
      calc
        toUnionChart Q x ≫ (imageContainingUnionMap C (selection Q) ≫ g) =
            (Q.theta x).hom ≫ (Q.W x).ι ≫ g := by
          simpa only [toUnionChart, imageContainingUnionMap, selection,
            imageContainingUnion, Category.assoc] using
            congrArg (fun k => (Q.theta x).hom ≫ k ≫ g)
              (Scheme.homOfLE_ι U (le_iSup Q.W x))
        _ = chartToS (Q.code x) := Q.overS x
    _ = (boundedAtlas Q).schemeGlueData.ι x ≫
        (boundedAtlas Q).gluedToS (coverCompat_of_chart_over_S (boundedAtlas Q)) :=
      (gluedToS_restricts (boundedAtlas Q)
        (coverCompat_of_chart_over_S (boundedAtlas Q)) x).symm

/-- Composition interface for MAIN: the supplied family must use the frozen
canonical base atlas. This constructs the frozen factor-layer input. -/
def adaptedComparison (Q : Family (canonicalBaseAtlas S) C) :
    CorrectedCommaCompositionData g C (selection Q) (unionLaw Q) where
  D := boundedAtlas Q
  ψ := comparison Q
  ψ_overS := comparison_overS Q

/-- Actual member of the frozen bounded comma family, using its repaired
factor maps and the theorem proving their over-T equation. -/
def boundedCommaObject (Q : Family (canonicalBaseAtlas S) C) :
    BoundedCommaFamily (A := canonicalBaseAtlas S) (f := f) V :=
  let c := adaptedComparison Q
  ⟨c.D, ⟨t c, t_overT c⟩⟩

/-- Unbundled entry point: no dependency on any chart-encoding worker leaf. -/
def comparisonOfCharts
    (W : SourceIndex V → U.Opens) (hW : ∀ x, IsAffineOpen (W x))
    (i : SourceIndex V → S.carrier)
    (code : ∀ x, ChartCode (canonicalBaseAtlas S) (i x))
    (theta : ∀ x, chartScheme (code x) ≅ (W x).toScheme)
    (overS : ∀ x, (theta x).hom ≫ (W x).ι ≫ g = chartToS (code x))
    (containsProjection : ∀ x, (commaInputProjection C).base x ∈ W x) :
    CorrectedCommaCompositionData g C
      { chartOpen := W, chartAffine := hW, containsProjection := containsProjection }
      (fun x => (le_iSup W x) (containsProjection x)) :=
  adaptedComparison
    { W := W, affine := hW, baseIndex := i, code := code, theta := theta,
      overS := overS, containsProjection := containsProjection }

end AlgebraicGeometry.Scheme.Etale.PullbackBounds.AdaptedGluing
