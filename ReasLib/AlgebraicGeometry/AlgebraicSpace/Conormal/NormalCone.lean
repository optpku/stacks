/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Symmetric

/-!
# Normal cones and normal bundles of immersions of algebraic spaces

The normal cone of an immersion of algebraic spaces is the relative spectrum of its
total conormal algebra. The normal bundle is the relative spectrum of the symmetric
algebra of its conormal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The normal cone of an immersion of algebraic spaces over `S`. -/
noncomputable def normalCone : AlgebraicSpace S :=
  relativeSpec (ConormalAlgebra.total i)

/-- The normal cone is the relative spectrum of the total conormal algebra. -/
theorem normalCone_eq_relativeSpec :
    normalCone i = relativeSpec (ConormalAlgebra.total i) :=
  rfl

/-- The structural morphism from the normal cone of an immersion to its source. -/
noncomputable def normalConeπ : normalCone i ⟶ Z :=
  relativeSpecπ (ConormalAlgebra.total i)

/-- The structure morphism of the normal cone is the relative-spectrum projection of
the total conormal algebra. -/
theorem normalConeπ_eq :
    normalConeπ i = relativeSpecπ (ConormalAlgebra.total i) :=
  rfl

/-- The structure morphism of the normal cone is affine. -/
instance instAffine_normalConeπ : Affine (normalConeπ i) :=
  (Affine.iff_representableAffine (relativeSpecπ (ConormalAlgebra.total i))).2
    ⟨relativeSpecπ_relativelyRepresentable (ConormalAlgebra.total i),
      relativeSpecπ_presheaf_affine (ConormalAlgebra.total i)⟩

/-- The normal bundle of an immersion of algebraic spaces over `S`. -/
noncomputable def normalBundle : AlgebraicSpace S :=
  relativeSpec (ConormalAlgebra.symmetric i)

/-- The normal bundle is the relative spectrum of the symmetric algebra of the
conormal sheaf. -/
theorem normalBundle_eq_relativeSpec :
    normalBundle i =
      relativeSpec (ConormalAlgebra.symmetric i) :=
  rfl

/-- The structural morphism from the normal bundle of an immersion to its source. -/
noncomputable def normalBundleπ : normalBundle i ⟶ Z :=
  relativeSpecπ (ConormalAlgebra.symmetric i)

/-- The structure morphism of the normal bundle is the relative-spectrum projection of
the symmetric algebra of the conormal sheaf. -/
theorem normalBundleπ_eq :
    normalBundleπ i =
      relativeSpecπ (ConormalAlgebra.symmetric i) :=
  rfl

/-- The structure morphism of the normal bundle is affine. -/
instance instAffine_normalBundleπ : Affine (normalBundleπ i) :=
  (Affine.iff_representableAffine (relativeSpecπ (ConormalAlgebra.symmetric i))).2
    ⟨relativeSpecπ_relativelyRepresentable (ConormalAlgebra.symmetric i),
      relativeSpecπ_presheaf_affine (ConormalAlgebra.symmetric i)⟩
/-- The canonical morphism from the normal cone of an immersion to its normal bundle. -/
noncomputable def normalConeToNormalBundle : normalCone i ⟶ normalBundle i :=
  relativeSpecMap (ConormalAlgebra.symmetricToTotal i)

/-- The comparison morphism is the relative spectrum of the symmetric-to-total conormal algebra
map. -/
theorem normalConeToNormalBundle_eq :
    normalConeToNormalBundle i =
      relativeSpecMap (ConormalAlgebra.symmetricToTotal i) :=
  rfl

/-- The canonical morphism from the normal cone to the normal bundle is a closed immersion. -/
instance instIsClosedImmersion_normalConeToNormalBundle :
    IsClosedImmersion (normalConeToNormalBundle i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
