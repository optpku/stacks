module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-! # Inverse images of open subspaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction of a morphism to an open subspace of its target, formed by
its functor-of-points fibre product with the open inclusion. -/
def restrictTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : OpenSubspace Y) :
    Open.inverseImage f U.ι U.isOpenImmersion.presheaf ⟶ U.X :=
  Open.inverseImageTo f U.ι U.isOpenImmersion.presheaf

namespace OpenSubspace

/-- The inverse image of an open subspace along a morphism of algebraic spaces. -/
def inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) : OpenSubspace Y where
  X := Open.inverseImage φ U.ι U.isOpenImmersion.presheaf
  ι := Open.inverseImageι φ U.ι U.isOpenImmersion.presheaf
  isOpenImmersion := ⟨Open.inverseImage_isOpenImmersion φ U.ι U.isOpenImmersion.presheaf⟩

/-- The inclusion of the inverse image is the first projection of the
functor-of-points fibre product. -/
theorem inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).ι = Open.inverseImageι φ U.ι U.isOpenImmersion.presheaf :=
  rfl

/-- The point-set of an inverse image is the preimage of the original point-set. -/
theorem inverseImage_pointsSet {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).pointsSet = Points.map φ ⁻¹' U.pointsSet :=
  sorry

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
