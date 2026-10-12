/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Inverse images of bundled open subspaces

The inverse image of an open subspace along a morphism of algebraic spaces is
the fibre-product open subspace, bundled as `OpenSubspace.ofι` of
`openInverseImageι`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace OpenSubspace

/-- The inclusion of an open subspace is an open immersion. -/
instance instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The inverse image of an open subspace along a morphism of algebraic spaces. -/
def inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) : OpenSubspace Y :=
  ofι (openInverseImageι φ U.ι)

/-- The inclusion of an inverse image is the unbundled inverse-image immersion. -/
theorem inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).ι = openInverseImageι φ U.ι :=
  sorry

/-- An inverse-image open subspace is the fibre-product open immersion
`openInverseImageι φ U.ι`. -/
theorem inverseImage_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).ι = openInverseImageι φ U.ι ∧
      IsOpenImmersion (U.inverseImage φ).ι :=
  sorry

/-- The point-set of an inverse image is the preimage of the original point-set. -/
theorem inverseImage_pointsSet {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).pointsSet = Points.map φ ⁻¹' U.pointsSet :=
  sorry

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
