module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.DiagonalRepresentable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.PairQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Descent.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineOnAffineSchemes

/-!
# The relative spectrum of an algebraic-space algebra

The original functor of base arrows and descended algebra maps has the actual
scheme atlas obtained by gluing section spectra. Its diagonal has the concrete
coincidence schemes constructed from relative equalizers. These supplied data
make it an algebraic space, with the projection that forgets the algebra map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The original descended algebra-point functor satisfies fppf descent. -/
theorem relativeSpectrumFunctor_isFppfSheaf (A : X.QcAlgebraUnder) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (relativeSpectrumFunctor A) := sorry

/-- The section-spectrum atlas supplies the actual scheme and map in the atlas condition. -/
theorem relativeSpectrumFunctor_hasAtlas (A : X.QcAlgebraUnder) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ relativeSpectrumFunctor A),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨relativeSpectrumDescentAtlas A, relativeSpectrumAtlasNat A,
    relativeSpectrumAtlasNat_presheaf_etale A, relativeSpectrumAtlasNat_locallySurjective A⟩

/-- The relative spectrum of a quasi-coherent `𝒪_X`-algebra, constructed from its actual atlas. -/
def relativeSpec (A : X.QcAlgebraUnder) : AlgebraicSpace S :=
  ofFunctor (relativeSpectrumFunctor A) (relativeSpectrumFunctor_isFppfSheaf A)
    (relativeSpectrumFunctor_representableDiagonal A) (relativeSpectrumFunctor_hasAtlas A)

/-- The functor of points retains the original base-arrow and descended-algebra-map pairs. -/
theorem relativeSpec_functorOfPoints (A : X.QcAlgebraUnder) :
    (relativeSpec A).functorOfPoints = relativeSpectrumFunctor A := rfl

/-- The structural morphism of the relative spectrum forgets the descended algebra data. -/
def relativeSpecπ (A : X.QcAlgebraUnder) : relativeSpec A ⟶ X where
  app T := TypeCat.ofHom fun p ↦ p.1
  naturality := sorry

/-- The structural morphism at a scheme point is its original base point. -/
theorem relativeSpecπ_app (A : X.QcAlgebraUnder) (T : (Over S)ᵒᵖ)
    (p : relativeSpectrumPair A T.unop) :
    (relativeSpecπ A).app T p = p.1 := rfl

/-- The original affine section-spectrum chart is an actual atlas of the relative spectrum. -/
def relativeSpecAtlas (A : X.QcAlgebraUnder) :
    ofOver (relativeSpectrumDescentAtlas A) ⟶ relativeSpec A :=
  relativeSpectrumAtlasNat A

/-- The relative-spectrum atlas projects through the stored atlas of the base. -/
theorem relativeSpecAtlas_toX (A : X.QcAlgebraUnder) :
    relativeSpecAtlas A ≫ relativeSpecπ A = relativeSpectrumDescentAtlasHomToX A := sorry

/-- The relative-spectrum projection is affine, as in the affine/algebra correspondence. -/
theorem relativeSpecπ_isAffine (A : X.QcAlgebraUnder) :
    isAffineOnAffineSchemes (relativeSpecπ A) := sorry

end AlgebraicGeometry.AlgebraicSpace
