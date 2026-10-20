module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.SchemeBase

/-!
# Explicit affine test pullbacks of the relative-spectrum projection

Base change to a supplied test scheme, restrict the pulled-back algebra to its
identity scheme chart, and use the native scheme relative spectrum. The
actual scheme and both projection maps form a limiting cone whose mediating
map is the native algebra-pushout point lift followed by the actual scheme
point inverse. These supply every representability witness of the projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The actual scheme representing the spectrum pullback along a supplied scheme-valued base map. -/
def relativeSpecPullbackScheme (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) : Over S :=
  relativeSpectrumSchemeOver (QcAlgebraUnder.baseChange g A)

/-- The actual pullback scheme projection to the supplied test scheme. -/
def relativeSpecPullbackToTest (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    relativeSpecPullbackScheme A g ⟶ T :=
  relativeSpectrumSchemeToBase (QcAlgebraUnder.baseChange g A)

/-- The actual pullback scheme map to the original relative spectrum. -/
def relativeSpecPullbackToSpectrum (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    yoneda.obj (relativeSpecPullbackScheme A g) ⟶ (relativeSpec A).functorOfPoints :=
  NatTrans.vcomp (relativeSpectrumSchemeNat (QcAlgebraUnder.baseChange g A))
    (homFunctor (relativeSpecBaseChangeMap g A))

/-- The actual scheme and spectrum projection maps satisfy the supplied base triangle. -/
theorem relativeSpecPullbackToSpectrum_w (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    NatTrans.vcomp (relativeSpecPullbackToSpectrum A g) (homFunctor (relativeSpecπ A)) =
      NatTrans.vcomp (yoneda.map (relativeSpecPullbackToTest A g)) (homFunctor g) := sorry

/-- The explicit test-scheme pullback cone has the actual native scheme as its vertex. -/
def relativeSpecPullbackCone (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    PullbackCone (homFunctor (relativeSpecπ A)) (homFunctor g) :=
  PullbackCone.mk (relativeSpecPullbackToSpectrum A g)
    (yoneda.map (relativeSpecPullbackToTest A g)) (relativeSpecPullbackToSpectrum_w A g)

/-- The mediating transformation uses the actual base-change point lift and native scheme inverse. -/
def relativeSpecPullbackConeLift (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X)
    (c : PullbackCone (homFunctor (relativeSpecπ A)) (homFunctor g)) :
    c.pt ⟶ yoneda.obj (relativeSpecPullbackScheme A g) :=
  relativeSpecBaseChangeConeLift g A c ≫ relativeSpectrumSchemeNatInverse (QcAlgebraUnder.baseChange g A)

/-- The represented test-scheme cone is limiting with its specified actual lift function. -/
def relativeSpecPullbackConeIsLimit (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    IsLimit (relativeSpecPullbackCone A g) :=
  PullbackCone.IsLimit.mk (C := (Over S)ᵒᵖ ⥤ Type u) (relativeSpecPullbackToSpectrum_w A g)
    (relativeSpecPullbackConeLift A g) sorry sorry sorry

/-- The relative-spectrum projection has an actual representing scheme and both maps for every test. -/
theorem relativeSpecπ_relativelyRepresentable (A : X.QcAlgebraUnder) :
    yoneda.relativelyRepresentable (homFunctor (relativeSpecπ A)) := by
  intro T g
  exact ⟨relativeSpecPullbackScheme A g, relativeSpecPullbackToTest A g,
    relativeSpecPullbackToSpectrum A g, IsPullback.of_isLimit (relativeSpecPullbackConeIsLimit A g)⟩

/-- The actual test-scheme projection is the native affine spectrum morphism. -/
theorem relativeSpecPullbackToTest_isAffineHom (A : X.QcAlgebraUnder) (g : ofOver T ⟶ X) :
    IsAffineHom (relativeSpecPullbackToTest A g).left :=
  Scheme.isAffineHom_of_realizesRelativeSpectrum _ (Scheme.relativeSpectrumRealization_realizes _)

/-- The structural projection is representably affine, with explicit test-scheme witnesses. -/
theorem relativeSpecπ_presheaf_affine (A : X.QcAlgebraUnder) :
    (MorphismProperty.over (@IsAffineHom : MorphismProperty Scheme.{u})).presheaf
      (homFunctor (relativeSpecπ A)) :=
  ⟨relativeSpecπ_relativelyRepresentable A, by
    intro T R g fst snd h_pullback
    sorry⟩

end AlgebraicGeometry.AlgebraicSpace
