module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.PairQuotient

/-!
# Explicit pullback witnesses for the relative-spectrum atlas

The pullback of the actual spectrum atlas along an original algebra point is
the supplied base-atlas pullback. Its maps are the concrete local spectrum
lift and test projection. The limiting cone lifts by the actual represented
base-atlas pullback, with no unspecified representing scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The concrete local atlas lift recovers the given original algebra point. -/
theorem relativeSpectrumPointAtlasLift_toFunctor (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) :
    yoneda.map (relativeSpectrumPointAtlasLift A p) ≫ relativeSpectrumAtlasNat A =
      yoneda.map (relativeSpectrumPointAtlasToTest A p) ≫ yonedaEquiv.symm p := sorry

/-- The concrete pullback cone for the atlas along an original relative-spectrum point. -/
def relativeSpectrumAtlasPointPullbackCone (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    PullbackCone (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p) :=
  PullbackCone.mk (yoneda.map (relativeSpectrumPointAtlasLift A p))
    (yoneda.map (relativeSpectrumPointAtlasToTest A p))
    (relativeSpectrumPointAtlasLift_toFunctor A p)

/-- Project every original spectrum point to its specified base point. -/
def relativeSpectrumFunctorToX (A : X.QcAlgebraUnder) : relativeSpectrumFunctor A ⟶ X.functorOfPoints where
  app T := TypeCat.ofHom fun p ↦ p.1
  naturality := sorry

/-- The actual atlas point transformation projects to its actual structural map to X. -/
theorem relativeSpectrumAtlasNat_toBase (A : X.QcAlgebraUnder) :
    relativeSpectrumAtlasNat A ≫ relativeSpectrumFunctorToX A = relativeSpectrumDescentAtlasToX A := sorry

/-- The original point transformation projects to the supplied original base arrow. -/
theorem relativeSpectrumPointNat_toBase (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    yonedaEquiv.symm p ≫ relativeSpectrumFunctorToX A = relativeSpectrumPointBase A p := sorry

/-- The actual mediating natural transformation into the represented base-atlas pullback. -/
def relativeSpectrumAtlasPointPullbackLift (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (c : PullbackCone (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p)) :
    c.pt ⟶ yoneda.obj (relativeSpectrumPointAtlasOver A p) :=
  ((atlasHom_presheaf_etale X).rep.isPullback (relativeSpectrumPointBase A p)).lift
    (c.fst ≫ yoneda.map
      (Over.homMk (Scheme.relativeSpectrumOver
        (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl))
    c.snd sorry

/-- The point-atlas pullback cone has the real represented-pullback lift operation. -/
def relativeSpectrumAtlasPointPullbackIsLimit (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    IsLimit (relativeSpectrumAtlasPointPullbackCone A p) :=
  PullbackCone.IsLimit.mk (relativeSpectrumPointAtlasLift_toFunctor A p)
    (relativeSpectrumAtlasPointPullbackLift A p) sorry sorry sorry

/-- The actual atlas has explicit representing schemes and both projection maps for every test point. -/
theorem relativeSpectrumAtlasNat_relativelyRepresentable (A : X.QcAlgebraUnder) :
    yoneda.relativelyRepresentable (relativeSpectrumAtlasNat A) := by
  intro T g
  let p : relativeSpectrumPair A T := yonedaEquiv g
  refine ⟨relativeSpectrumPointAtlasOver A p, relativeSpectrumPointAtlasToTest A p,
    yoneda.map (relativeSpectrumPointAtlasLift A p), ?_⟩
  have hp := IsPullback.of_isLimit (relativeSpectrumAtlasPointPullbackIsLimit A p)
  change IsPullback (yoneda.map (relativeSpectrumPointAtlasLift A p))
    (yoneda.map (relativeSpectrumPointAtlasToTest A p))
    (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p) at hp
  simpa only [p, Equiv.symm_apply_apply] using hp

/-- The concrete atlas is representably étale by its stored-atlas pullback projections. -/
theorem relativeSpectrumAtlasNat_presheaf_etale (A : X.QcAlgebraUnder) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (relativeSpectrumAtlasNat A) :=
  ⟨relativeSpectrumAtlasNat_relativelyRepresentable A, by
    intro T R g fst snd h_pullback
    sorry⟩

/-- The concrete atlas covers the original spectrum-point functor in the étale topology. -/
theorem relativeSpectrumAtlasNat_locallySurjective (A : X.QcAlgebraUnder) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (relativeSpectrumAtlasNat A) := sorry

end AlgebraicGeometry.AlgebraicSpace
