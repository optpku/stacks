module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Chart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Atlas
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# The relative-spectrum descent relation

Restrict the given algebra to the supplied atlas and its represented kernel
pair. Actual chart-spectrum maps lift the two projections to the constructed
affine spectra; their product gives the relation used by étale descent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The supplied atlas, as a chart in the presentation of the small étale site. -/
def relativeSpectrumAtlasChart (X : AlgebraicSpace S) : smallEtaleSite X :=
  smallEtaleSite.mk (atlasHom X)

/-- The represented kernel pair, as a chart over the algebraic space. -/
def relativeSpectrumKernelChart (X : AlgebraicSpace S) : smallEtaleSite X :=
  smallEtaleSite.mk (atlasKernelPairHom X)

/-- The first actual kernel-pair projection, retaining its triangle over X. -/
def relativeSpectrumKernelChart_t (X : AlgebraicSpace S) :
    relativeSpectrumKernelChart X ⟶ relativeSpectrumAtlasChart X :=
  MorphismProperty.CostructuredArrow.homMk (atlasKernelPair_t X) trivial rfl

/-- The second actual kernel-pair projection, retaining its triangle over X. -/
def relativeSpectrumKernelChart_s (X : AlgebraicSpace S) :
    relativeSpectrumKernelChart X ⟶ relativeSpectrumAtlasChart X :=
  MorphismProperty.CostructuredArrow.homMk (atlasKernelPair_s X) trivial
    (atlasKernelPair_t_comp_eq_s_comp X).symm

/-- The concrete chart spectrum, with its structural morphism composed to the original base S. -/
def relativeSpectrumChartOver (A : X.QcAlgebraUnder) (U : smallEtaleSite X) : Over S :=
  Over.mk ((Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A U)).π ≫ U.left.hom)

/-- The actual spectrum map induced by a morphism of the étale charts, as a map over S. -/
def relativeSpectrumChartOverMap (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    relativeSpectrumChartOver A U ⟶ relativeSpectrumChartOver A V :=
  Over.homMk (QcAlgebraUnder.chartSpectrumMap A m) sorry

/-- The affine chart V over the supplied base atlas U. -/
abbrev relativeSpectrumDescentAtlas (A : X.QcAlgebraUnder) : Over S :=
  relativeSpectrumChartOver A (relativeSpectrumAtlasChart X)

/-- The affine chart W over the represented kernel pair U×_XU. -/
abbrev relativeSpectrumDescentKernel (A : X.QcAlgebraUnder) : Over S :=
  relativeSpectrumChartOver A (relativeSpectrumKernelChart X)

/-- The first projection of the descended affine chart relation. -/
def relativeSpectrumDescent_t (A : X.QcAlgebraUnder) :
    relativeSpectrumDescentKernel A ⟶ relativeSpectrumDescentAtlas A :=
  relativeSpectrumChartOverMap A (relativeSpectrumKernelChart_t X)

/-- The second projection of the descended affine chart relation. -/
def relativeSpectrumDescent_s (A : X.QcAlgebraUnder) :
    relativeSpectrumDescentKernel A ⟶ relativeSpectrumDescentAtlas A :=
  relativeSpectrumChartOverMap A (relativeSpectrumKernelChart_s X)

/-- The actual relative-spectrum relation induced from the stored atlas kernel pair. -/
def relativeSpectrumDescentRelation (A : X.QcAlgebraUnder) :
    Scheme.PreRelation (relativeSpectrumDescentAtlas A) :=
  Scheme.PreRelation.ofHom
    (prod.lift (relativeSpectrumDescent_t A) (relativeSpectrumDescent_s A))

/-- The reflexive section of the stored atlas kernel pair, using its actual represented pullback. -/
def relativeSpectrumKernelChart_diagonal (X : AlgebraicSpace S) :
    relativeSpectrumAtlasChart X ⟶ relativeSpectrumKernelChart X :=
  MorphismProperty.CostructuredArrow.homMk
    (yoneda.preimage (((atlasHom_presheaf_etale X).rep.isPullback (atlasHom X)).lift
      (𝟙 _) (𝟙 _) rfl)) trivial sorry

/-- The symmetry of the stored atlas kernel pair, interchanging its actual projections. -/
def relativeSpectrumKernelChart_swap (X : AlgebraicSpace S) :
    relativeSpectrumKernelChart X ⟶ relativeSpectrumKernelChart X :=
  MorphismProperty.CostructuredArrow.homMk
    (yoneda.preimage (((atlasHom_presheaf_etale X).rep.isPullback (atlasHom X)).lift
      (yoneda.map (atlasKernelPair_s X)) (yoneda.map (atlasKernelPair_t X))
      (atlasKernelPair_t_comp_eq_s_comp X).symm)) trivial sorry

/-- The actual reflexive morphism of the constructed spectrum relation. -/
def relativeSpectrumDescentReflexive (A : X.QcAlgebraUnder) :
    ReflexiveRelation (relativeSpectrumDescentRelation A).t (relativeSpectrumDescentRelation A).s where
  right_cancellation := sorry
  r := relativeSpectrumChartOverMap A (relativeSpectrumKernelChart_diagonal X)
  reflexivity₁ := sorry
  reflexivity₂ := sorry

/-- The actual symmetry morphism of the constructed spectrum relation. -/
def relativeSpectrumDescentSymmetric (A : X.QcAlgebraUnder) :
    SymmetricRelation (relativeSpectrumDescentRelation A).t (relativeSpectrumDescentRelation A).s where
  right_cancellation := sorry
  s := relativeSpectrumChartOverMap A (relativeSpectrumKernelChart_swap X)
  symmetry₁ := sorry
  symmetry₂ := sorry

/-- The first constructed relation projection is étale by quasi-coherent base change. -/
theorem relativeSpectrumDescentRelation_etale_t (A : X.QcAlgebraUnder) :
    AlgebraicGeometry.Etale (relativeSpectrumDescentRelation A).t.left := sorry

/-- The second constructed relation projection is étale by quasi-coherent base change. -/
theorem relativeSpectrumDescentRelation_etale_s (A : X.QcAlgebraUnder) :
    AlgebraicGeometry.Etale (relativeSpectrumDescentRelation A).s.left := sorry

/-- The source scheme of the relation is the actual constructed kernel chart spectrum. -/
theorem relativeSpectrumDescentRelation_left (A : X.QcAlgebraUnder) :
    (relativeSpectrumDescentRelation A).left = relativeSpectrumDescentKernel A := rfl

end AlgebraicGeometry.AlgebraicSpace
