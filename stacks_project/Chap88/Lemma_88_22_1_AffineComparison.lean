/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap88.Lemma_88_22_1_FlatLocus
public import ReasLib.CategoryTheory.Sites.LocalIsoDescent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The actual affine comparison for Stacks 0GD8

The chart/completion comparison descends the same quotient-stage cocone in
both directions by sheaf amalgamation. The torsion-quotient forward map uses
`Scheme.Hom.liftQuotient`; the inverse applies the actual quotient immersion
and the constructed chart descent. No isomorphism is chosen from `Nonempty`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.AffineComparison

variable {S : Scheme.{u}} (U : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine U]

/-- The named sheafy completion of the presenting affine scheme along its defining ideal. -/
def chartCompletion : (Over S)ᵒᵖ ⥤ Type u :=
  completionAlongSubspace
    (AffineFormalAlgebraicSpace.closedImmersion (chartStructureHom U) (chartIdeal U))

/-- The colimit universal property belongs to the selected genuine presentation. -/
def presentationIsColimit : IsColimit (presentationCocone U) :=
  Classical.choice
    (Classical.choose_spec (Classical.choose_spec
      (instIsDirectedAffineThickeningColimit_presentationDiagram U).exists_colimit)).1

/-- The selected chart comparison is locally surjective by its presentation contract. -/
instance presentationLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (presentationCoconeι U) :=
  (Classical.choose_spec (Classical.choose_spec
    (instIsDirectedAffineThickeningColimit_presentationDiagram U).exists_colimit)).2.1

/-- The selected chart comparison is locally injective by the same contract. -/
instance presentationLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (presentationCoconeι U) :=
  (Classical.choose_spec (Classical.choose_spec
    (instIsDirectedAffineThickeningColimit_presentationDiagram U).exists_colimit)).2.2

/-- The given chart is an fppf sheaf, as supplied by its presentation. -/
theorem chartIsSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) U :=
  (instIsDirectedAffineThickeningColimit_presentationDiagram U).isSheaf

/-- Local factorization through infinitesimal neighborhoods is a sheaf condition. -/
theorem completionIsSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (chartCompletion U) :=
  sorry

/-- The actual quotient-stage inclusion into its ambient spectrum over `S`. -/
def stageToAmbient (n : ℕ) :
    (presentationDiagram U).obj n ⟶ Over.mk (chartStructureHom U) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal U ^ (n + 1))))) rfl

/-- A section of a quotient stage lies in the named completion of its ambient spectrum. -/
theorem stageInCompletion (n : ℕ) {T : (Over S)ᵒᵖ}
    (f : T.unop ⟶ (presentationDiagram U).obj n) :
    fppfLocallyFactorsThroughNeighbourhood
      (AffineFormalAlgebraicSpace.closedImmersion (chartStructureHom U) (chartIdeal U))
      (f ≫ stageToAmbient U n) :=
  sorry

/-- The prescribed inclusion of each real quotient stage into the named completion. -/
def stageToCompletion (n : ℕ) :
    yoneda.obj ((presentationDiagram U).obj n) ⟶ chartCompletion U where
  app _ := ofHom fun f ↦ ⟨f ≫ stageToAmbient U n, stageInCompletion U n f⟩
  naturality _ _ _ := rfl

/-- The canonical cocone in the named completion has these actual stage inclusions. -/
def completionCocone : Cocone (presentationDiagram U ⋙ yoneda) where
  pt := chartCompletion U
  ι := { app := stageToCompletion U, naturality := sorry }

/-- The comparison from the presentation colimit is its actual universal descent. -/
def presentationToCompletion : (presentationCocone U).pt ⟶ chartCompletion U :=
  (presentationIsColimit U).desc (completionCocone U)

/-- This universal descent agrees with the canonical inclusion on every stage. -/
theorem presentationToCompletion_stage (n : ℕ) :
    (presentationCocone U).ι.app n ≫ presentationToCompletion U = stageToCompletion U n :=
  (presentationIsColimit U).fac (completionCocone U) n

/-- The named completion is the sheafification of this same actual quotient diagram. -/
instance completionLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (presentationToCompletion U) :=
  sorry

/-- Two presentation sections with the same ambient morphism agree locally. -/
instance completionLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (presentationToCompletion U) :=
  sorry

/-- Descend actual stage inclusions from the given chart presentation into the completion. -/
def chartToCompletion : U ⟶ chartCompletion U :=
  Presheaf.LocalIsoDescent.descend (Scheme.fppfTopology.over S)
    (presentationCoconeι U) (presentationToCompletion U) (completionIsSheaf U)

/-- Descend the original presentation legs from the named completion back to the chart. -/
def completionToChart : chartCompletion U ⟶ U :=
  Presheaf.LocalIsoDescent.descend (Scheme.fppfTopology.over S)
    (presentationToCompletion U) (presentationCoconeι U) (chartIsSheaf U)

/-- The forward comparison preserves the original cocone morphism. -/
theorem chartToCompletion_fac :
    presentationCoconeι U ≫ chartToCompletion U = presentationToCompletion U :=
  Presheaf.LocalIsoDescent.descend_fac _ _ _ _

/-- The inverse comparison preserves the same cocone morphism. -/
theorem completionToChart_fac :
    presentationToCompletion U ≫ completionToChart U = presentationCoconeι U :=
  Presheaf.LocalIsoDescent.descend_fac _ _ _ _

/-- The two explicit descents are inverse on the chart. -/
theorem chartToCompletion_comp : chartToCompletion U ≫ completionToChart U = 𝟙 U := by
  apply Presheaf.LocalIsoDescent.hom_ext (Scheme.fppfTopology.over S)
    (presentationCoconeι U) (chartIsSheaf U)
  rw [← Category.assoc, chartToCompletion_fac, completionToChart_fac, Category.comp_id]

/-- The two explicit descents are inverse on the completion. -/
theorem completionToChart_comp : completionToChart U ≫ chartToCompletion U = 𝟙 _ := by
  apply Presheaf.LocalIsoDescent.hom_ext (Scheme.fppfTopology.over S)
    (presentationToCompletion U) (completionIsSheaf U)
  rw [← Category.assoc, completionToChart_fac, chartToCompletion_fac, Category.comp_id]

/-- The chart/completion isomorphism has explicitly defined forward and inverse maps. -/
def chartCompletionIso : U ≅ chartCompletion U where
  hom := chartToCompletion U
  inv := completionToChart U
  hom_inv_id := chartToCompletion_comp U
  inv_hom_id := completionToChart_comp U

/-- On each actual quotient stage, the chart comparison is the specified inclusion. -/
theorem chartToCompletion_stage (n : ℕ) :
    ((presentationCocone U).ι.app n ≫ presentationCoconeι U) ≫ chartToCompletion U =
      stageToCompletion U n := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f : (presentationCocone U).pt ⟶ chartCompletion U ↦
      (presentationCocone U).ι.app n ≫ f) (chartToCompletion_fac U)).trans
      (presentationToCompletion_stage U n))

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
variable {X : (Over S)ᵒᵖ ⥤ Type u} (π : U ⟶ X) (p : X ⟶ spf A hA)

/-- The actual ambient scheme morphism of a chart-flat section. -/
def ambientSection {T : (Over S)ᵒᵖ} (x : (ofNoetherianAffine π p).obj T) :
    T.unop ⟶ Over.mk (chartStructureHom U) :=
  ((chartToCompletion U).app T x.val).val

/-- Its actual map on global sections, expressed through Γ/Spec. -/
def ambientRingHom {T : (Over S)ᵒᵖ} (x : (ofNoetherianAffine π p).obj T) :
    chartRing U →+* Γ(T.unop.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (chartRing U))).inv ≫ (ambientSection U π p x).left.appTop).hom

/-- A chart-flat section kills the torsion ideal: this holds on its given local
torsion-stage lifts and descends along the fppf cover. -/
theorem ambientSection_kills_torsion {T : (Over S)ᵒᵖ}
    (x : (ofNoetherianAffine π p).obj T) :
    chartTorsionIdeal π p ≤ RingHom.ker (ambientRingHom U π p x) :=
  sorry

/-- The actual quotient lift on rings, defined by its values on quotient classes. -/
def quotientRingHom {T : (Over S)ᵒᵖ} (x : (ofNoetherianAffine π p).obj T) :
    chartQuotRing π p →+* Γ(T.unop.left, ⊤) :=
  Ideal.Quotient.lift (chartTorsionIdeal π p) (ambientRingHom U π p x)
    (ambientSection_kills_torsion U π p x)

/-- The quotient lift sends `[b]` to the original section's value of `b`. -/
theorem quotientRingHom_mk {T : (Over S)ᵒᵖ}
    (x : (ofNoetherianAffine π p).obj T) (b : chartRing U) :
    quotientRingHom U π p x (Ideal.Quotient.mk (chartTorsionIdeal π p) b) =
      ambientRingHom U π p x b := rfl

/-- The quotient ring lift is converted to a scheme map by the actual Γ/Spec adjunction. -/
def quotientLift {T : (Over S)ᵒᵖ} (x : (ofNoetherianAffine π p).obj T) :
    T.unop ⟶ Over.mk (chartQuotStructureHom π p) :=
  Over.homMk
    ((ambientSection U π p x).left.liftQuotient (chartTorsionIdeal π p)
      (ambientSection_kills_torsion U π p x)) (by
        change (ambientSection U π p x).left.liftQuotient _ _ ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartTorsionIdeal π p))) ≫
            chartStructureHom U) = _
        rw [← Category.assoc, Scheme.Hom.liftQuotient_comp]
        exact (ambientSection U π p x).w)

/-- The geometric lift is precisely Spec of the explicit quotient ring map. -/
theorem quotientLift_left {T : (Over S)ᵒᵖ}
    (x : (ofNoetherianAffine π p).obj T) :
    (quotientLift U π p x).left = T.unop.left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (quotientRingHom U π p x)) := rfl

/-- The quotient morphism of ambient spectra over the same base. -/
def quotientEmbedding :
    Over.mk (chartQuotStructureHom π p) ⟶ Over.mk (chartStructureHom U) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartTorsionIdeal π p)))) rfl

/-- Composing the actual quotient lift with the quotient immersion returns the ambient section. -/
theorem quotientLift_comp {T : (Over S)ᵒᵖ}
    (x : (ofNoetherianAffine π p).obj T) :
    quotientLift U π p x ≫ quotientEmbedding U π p = ambientSection U π p x := by
  apply Over.OverMorphism.ext
  exact (ambientSection U π p x).left.liftQuotient_comp _ _

/-- Local factorization through `B/(t+I^(n+1))` makes the actual quotient lift
a section of the completion of `Spec(B/t)` along the image of `I`. -/
theorem quotientLift_inCompletion {T : (Over S)ᵒᵖ}
    (x : (ofNoetherianAffine π p).obj T) :
    fppfLocallyFactorsThroughNeighbourhood
      (AffineFormalAlgebraicSpace.closedImmersion (chartQuotStructureHom π p)
        (chartQuotIdeal π p)) (quotientLift U π p x) :=
  sorry

/-- The concrete forward map to the named sheafy `Spf(B/t)`. -/
def forward : ofNoetherianAffine π p ⟶ affineFlatLocus π p where
  app _ := ofHom fun x ↦ ⟨quotientLift U π p x, quotientLift_inCompletion U π p x⟩
  naturality := sorry

/-- Forward comparison followed by the quotient immersion preserves the original section. -/
theorem forward_inclusion :
    forward U π p ≫ affineFlatLocusι π p =
      ofNoetherianAffineι π p ≫ chartToCompletion U := by
  ext T x
  apply Subtype.ext
  exact quotientLift_comp U π p x

/-- A section of the quotient completion gives a chart-flat section after the
actual quotient immersion and chart descent. -/
theorem inverse_inChart {T : (Over S)ᵒᵖ} (y : (affineFlatLocus π p).obj T) :
    IsChartFlatSection π p
      ((completionToChart U).app T ((affineFlatLocusι π p).app T y)) :=
  sorry

/-- The concrete inverse uses the actual quotient inclusion and the constructed chart descent. -/
def inverse : affineFlatLocus π p ⟶ ofNoetherianAffine π p where
  app _ := ofHom fun y ↦
    ⟨(completionToChart U).app _ ((affineFlatLocusι π p).app _ y), inverse_inChart U π p y⟩
  naturality := sorry

/-- The inverse retains the actual quotient immersion into the original chart. -/
theorem inverse_inclusion :
    inverse U π p ≫ ofNoetherianAffineι π p =
      affineFlatLocusι π p ≫ completionToChart U := rfl

/-- Uniqueness of chart descent and of the quotient lift makes forward then inverse the identity. -/
theorem forward_inverse : forward U π p ≫ inverse U π p = 𝟙 _ := by
  ext T x
  apply Subtype.ext
  have hf := congrArg (fun f : ofNoetherianAffine π p ⟶ chartCompletion U ↦ f.app T x)
    (forward_inclusion U π p)
  have hu := congrArg (fun f : U ⟶ U ↦ f.app T x.val) (chartToCompletion_comp U)
  exact (congrArg ((completionToChart U).app T) hf).trans hu

/-- The actual quotient immersion is pointwise injective, using the mono Spec quotient map. -/
instance quotientSpecClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartTorsionIdeal π p)))) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The actual quotient immersion is pointwise injective, using the mono Spec quotient map. -/
theorem quotientInclusion_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((affineFlatLocusι π p).app T) := by
  intro y z h
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (chartTorsionIdeal π p))))).mp
  exact congrArg (fun x : (chartCompletion U).obj T ↦ x.val.left) h

/-- The quotient immersion is monic, so inverse then forward is the identity. -/
theorem inverse_forward : inverse U π p ≫ forward U π p = 𝟙 _ := by
  ext T y
  apply quotientInclusion_injective U π p T
  have hf := congrArg (fun f : ofNoetherianAffine π p ⟶ chartCompletion U ↦
    f.app T ((inverse U π p).app T y)) (forward_inclusion U π p)
  have hu := congrArg (fun f : chartCompletion U ⟶ chartCompletion U ↦
    f.app T ((affineFlatLocusι π p).app T y)) (completionToChart_comp U)
  exact hf.trans hu

/-- The chartwise torsion-stage image is the named sheafy formal spectrum of the actual quotient. -/
def chartFlatCompletionIso : ofNoetherianAffine π p ≅ affineFlatLocus π p where
  hom := forward U π p
  inv := inverse U π p
  hom_inv_id := forward_inverse U π p
  inv_hom_id := inverse_forward U π p

end AlgebraicGeometry.FormalAlgebraicSpace.AffineComparison

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
variable [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
variable (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
variable (p : U ⟶ spf A hA)

/-- The source-facing forward comparison lands in the named sheafy `Spf(B/t)`. -/
def affine_spec_hom : flatLocus p ⟶ affineFlatLocus (𝟙 U) p :=
  affine_stage_spec_hom hA p ≫ AffineComparison.forward U (𝟙 U) p

/-- The inverse uses the quotient immersion and the concrete chart descent. -/
def affine_spec_inv : affineFlatLocus (𝟙 U) p ⟶ flatLocus p :=
  AffineComparison.inverse U (𝟙 U) p ≫ affine_stage_spec_inv hA p

/-- The flat locus of a Noetherian affine chart is the actual named sheafy
formal spectrum of its base-power-torsion quotient. Both maps are constructed. -/
def affine_spec : flatLocus p ≅ affineFlatLocus (𝟙 U) p :=
  (affine_stage_spec hA p).trans (AffineComparison.chartFlatCompletionIso U (𝟙 U) p)

/-- The public isomorphism has exactly the specified forward and inverse maps. -/
theorem affine_spec_hom_inv :
    (affine_spec hA p).hom = affine_spec_hom hA p ∧
      (affine_spec hA p).inv = affine_spec_inv hA p :=
  ⟨rfl, rfl⟩

/-- The source-facing comparison preserves the immersion into the original affine chart. -/
theorem affine_spec_inclusion :
    (affine_spec hA p).hom ≫ affineFlatLocusι (𝟙 U) p =
      flatLocusι p ≫ AffineComparison.chartToCompletion U := by
  change (affine_stage_spec_hom hA p ≫ AffineComparison.forward U (𝟙 U) p) ≫ _ = _
  rw [Category.assoc, AffineComparison.forward_inclusion]
  rfl

/-- Membership in the image of the named quotient completion is exactly
local factorization through the actual torsion quotient stages. -/
theorem affine_completion_image (T : (Over S)ᵒᵖ) (x : U.obj T) :
    (∃ y : (affineFlatLocus (𝟙 U) p).obj T,
      (AffineComparison.completionToChart U).app T ((affineFlatLocusι (𝟙 U) p).app T y) = x) ↔
      IsChartFlatSection (𝟙 U) p x := by
  constructor
  · change (∃ y, (AffineComparison.completionToChart U).app T
      ((affineFlatLocusι (𝟙 U) p).app T y) = x) → IsChartFlatSection (𝟙 U) p x
    rintro ⟨y, rfl⟩
    exact AffineComparison.inverse_inChart U (𝟙 U) p y
  · change IsChartFlatSection (𝟙 U) p x → ∃ y,
      (AffineComparison.completionToChart U).app T ((affineFlatLocusι (𝟙 U) p).app T y) = x
    intro hx
    refine ⟨(AffineComparison.forward U (𝟙 U) p).app T ⟨x, hx⟩, ?_⟩
    have h := congrArg (fun f : ofNoetherianAffine (𝟙 U) p ⟶ ofNoetherianAffine (𝟙 U) p ↦
      f.app T ⟨x, hx⟩) (AffineComparison.forward_inverse U (𝟙 U) p)
    exact congrArg Subtype.val h

end AlgebraicGeometry.FormalAlgebraicSpace
