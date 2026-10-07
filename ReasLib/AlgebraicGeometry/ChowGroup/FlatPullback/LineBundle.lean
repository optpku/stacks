module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.AffineBundle
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle

/-!
# Flat pullback along line bundles

This file records homotopy invariance for Chow groups along the projection of the vector bundle
associated to an invertible module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Pullback along the vector bundle associated to an invertible module is a bijection from
degree `k` Chow homology of the base to degree `k + 1` Chow homology of the total space. -/
theorem flatPullback_bijective_associatedVectorBundle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P] (k : ℤ) :
    -- Local instance justification (proof-local temporary data): the named local-finite-type proof is installed only within this closed Prop result because flatPullback consumes this class.
    letI : LocallyOfFiniteType
        (Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom)).hom :=
      Scheme.associatedVectorBundleOver_locallyOfFiniteType X ℒ P
    -- Local instance justification (proof-local temporary data): the named flatness proof is installed only within this closed Prop result because flatPullback consumes this class.
    letI : Flat
        (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) :=
      Scheme.associatedVectorBundleOverHom_flat X ℒ P rfl
    -- Local instance justification (proof-local temporary data): the named relative-dimension proof is installed only within this closed Prop result because flatPullback consumes this class.
    letI : Scheme.Hom.RelativeDimension
        (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) 1 :=
      Scheme.associatedVectorBundleOverHom_relativeDimension X ℒ P rfl
    Function.Bijective
      (flatPullback δ
        (Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom)) X
        (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)
        1 k) := sorry

end AlgebraicGeometry.ChowGroup
