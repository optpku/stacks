module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.LineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.32.2: pullback along the vector bundle associated to an invertible module induces
a bijection from degree `k` Chow homology of the base to degree `k + 1` Chow homology of the
total space. -/
@[stacks 0B74] #check
  (AlgebraicGeometry.ChowGroup.flatPullback_bijective_associatedVectorBundle :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P] (k : ℤ),
    -- Local instance justification (proof-local temporary data): the named local-finite-type proof is installed only in this complete Prop-valued source check because flatPullback consumes this class.
    letI : LocallyOfFiniteType
        (Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom)).hom :=
      Scheme.associatedVectorBundleOver_locallyOfFiniteType X ℒ P
    -- Local instance justification (proof-local temporary data): the named flatness proof is installed only in this complete Prop-valued source check because flatPullback consumes this class.
    letI : Flat
        (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) :=
      Scheme.associatedVectorBundleOverHom_flat X ℒ P rfl
    -- Local instance justification (proof-local temporary data): the named relative-dimension proof is installed only in this complete Prop-valued source check because flatPullback consumes this class.
    letI : Scheme.Hom.RelativeDimension
        (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) 1 :=
      Scheme.associatedVectorBundleOverHom_relativeDimension X ℒ P rfl
    Function.Bijective
      (AlgebraicGeometry.ChowGroup.flatPullback δ
        (Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom)) X
        (Over.homMk (Scheme.associatedVectorBundleπ ℒ P) rfl :
          Over.mk (Scheme.associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)
        1 k))
