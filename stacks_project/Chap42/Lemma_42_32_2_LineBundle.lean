module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- The associated line-bundle projection is flat. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleπ_flat :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P],
    Flat (associatedVectorBundleπ ℒ P))

/- The associated line-bundle projection has relative dimension one. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleπ_relativeDimension :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P],
    Hom.RelativeDimension (associatedVectorBundleπ ℒ P) 1)

/- The associated line-bundle projection is locally of finite type. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleπ_locallyOfFiniteType :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P],
    LocallyOfFiniteType (associatedVectorBundleπ ℒ P))

/- The associated line bundle is locally an affine one-space over its base. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleπ_localAffineSpace :
  ∀ {X : Scheme.{u}} (ℒ : X.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P],
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Over.mk (associatedVectorBundleπ ℒ P ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin 1); U.toScheme) ↘ U.toScheme)))

/- The associated line-bundle total space remains locally of finite type over a common base. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleOver_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P],
    LocallyOfFiniteType (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom)

/- The over-category projection of the associated line bundle is flat. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleOverHom_flat :
  ∀ {S : Scheme.{u}} (X : Over S)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P]
    (w : associatedVectorBundleπ ℒ P ≫ X.hom =
      (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom),
    Flat (Over.Hom.left (Over.homMk (associatedVectorBundleπ ℒ P) w :
      Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)))

/- The over-category projection of the associated line bundle has relative dimension one. -/
#check (AlgebraicGeometry.Scheme.associatedVectorBundleOverHom_relativeDimension :
  ∀ {S : Scheme.{u}} (X : Over S)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P]
    (w : associatedVectorBundleπ ℒ P ≫ X.hom =
      (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom),
    Hom.RelativeDimension
      (Over.Hom.left (Over.homMk (associatedVectorBundleπ ℒ P) w :
        Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) 1)

end AlgebraicGeometry.Scheme
