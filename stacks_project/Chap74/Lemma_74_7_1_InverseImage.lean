/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Inverse images of bundled open subspaces

The inverse image of an open subspace along a morphism of algebraic spaces is
the fibre-product open subspace with its first projection as inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace OpenSubspace

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X), OpenSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.inverseImage_ι :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X),
    (U.inverseImage φ).ι = Open.inverseImageι φ U.ι U.isOpenImmersion.presheaf)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.inverseImage_pointsSet :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X),
    (U.inverseImage φ).pointsSet = Points.map φ ⁻¹' U.pointsSet)

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
