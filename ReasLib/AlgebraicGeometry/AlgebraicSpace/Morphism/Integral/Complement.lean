module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Open complements of images of integral morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A section of the functor of points of `X` misses the image of `f` when the induced map on
points lands in the complement of `f(|Y|)`. -/
def missesImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : Prop :=
  pointsImage (homOfYonedaSection α) ⊆ (pointsImage f)ᶜ

/-- Missing the image of `f` is the point-set condition on the Yoneda morphism associated to a
section. -/
theorem missesImage_iff {X Y : AlgebraicSpace S} (f : Y ⟶ X) {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) :
    missesImage f α ↔ pointsImage (homOfYonedaSection α) ⊆ (pointsImage f)ᶜ :=
  Iff.rfl

/-- The image of `|Y|` along an integral morphism is a closed subset of `|X|`. -/
theorem isClosed_pointsImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    IsClosed (pointsImage f) :=
  sorry

/-- The subfunctor of maps into `X` whose image of points misses `f(|Y|)`. -/
def imageComplementSubfunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    Subfunctor X.functorOfPoints :=
  OpenSubspace.Construction.subfunctor X
    ⟨(pointsImage f)ᶜ, (isClosed_pointsImage f).isOpen_compl⟩

/-- Membership in the image-complement subfunctor is the missing-image condition. -/
theorem mem_imageComplementSubfunctor_obj {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    α ∈ (imageComplementSubfunctor f).obj U ↔ missesImage f α :=
  Iff.rfl

/-- The open complement algebraic space `|X| \ f(|Y|)` of an integral morphism `f : Y ⟶ X`. -/
def imageComplement {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    AlgebraicSpace S :=
  OpenSubspace.Construction.space X
    ⟨(pointsImage f)ᶜ, (isClosed_pointsImage f).isOpen_compl⟩

/-- The functor of points of the image complement is the missing-`f(|Y|)` subfunctor. -/
theorem imageComplement_functorOfPoints {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] :
    (imageComplement f).functorOfPoints = (imageComplementSubfunctor f).toFunctor :=
  rfl

/-- The open immersion of the image complement `|X| \ f(|Y|)` into `X`. -/
def imageComplementι {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    imageComplement f ⟶ X :=
  OpenSubspace.Construction.ι X
    ⟨(pointsImage f)ᶜ, (isClosed_pointsImage f).isOpen_compl⟩

/-- The image-complement inclusion is the subfunctor inclusion of maps missing `f(|Y|)`. -/
theorem imageComplementι_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    imageComplementι f = (imageComplementSubfunctor f).ι :=
  rfl

/-- The image of the complement algebraic space in `|X|` is the complement of `f(|Y|)`. -/
theorem imageComplement_range {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    pointsImage (imageComplementι f) = (pointsImage f)ᶜ :=
  OpenSubspace.Construction.inclusion_range X
    ⟨(pointsImage f)ᶜ, (isClosed_pointsImage f).isOpen_compl⟩

/-- The complement of the image of an integral morphism, as an open subspace of `X`. -/
def imageComplementSubspace {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsIntegralHom f] :
    OpenSubspace X :=
  OpenSubspace.fromOpens
    ⟨(pointsImage f)ᶜ, (isClosed_pointsImage f).isOpen_compl⟩

end AlgebraicGeometry.AlgebraicSpace
