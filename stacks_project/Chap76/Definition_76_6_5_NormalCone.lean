module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.NormalCone

/-!
# Normal cones and normal bundles of immersions of algebraic spaces

The normal cone is the relative spectrum of the total conormal algebra. The
normal bundle is the relative spectrum of the symmetric algebra of the conormal sheaf.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

#check (AlgebraicGeometry.AlgebraicSpace.normalCone_eq_relativeSpec i :
  normalCone i = relativeSpec (ConormalAlgebra.total i))

#check (AlgebraicGeometry.AlgebraicSpace.normalConeπ_eq i :
  normalConeπ i = relativeSpecπ (ConormalAlgebra.total i))

#check (AlgebraicGeometry.AlgebraicSpace.instAffine_normalConeπ i : Affine (normalConeπ i))

#check (AlgebraicGeometry.AlgebraicSpace.normalBundle_eq_relativeSpec i :
  normalBundle i = relativeSpec (ConormalAlgebra.symmetric i))

#check (AlgebraicGeometry.AlgebraicSpace.normalBundleπ_eq i :
  normalBundleπ i = relativeSpecπ (ConormalAlgebra.symmetric i))

#check (AlgebraicGeometry.AlgebraicSpace.instAffine_normalBundleπ i : Affine (normalBundleπ i))
