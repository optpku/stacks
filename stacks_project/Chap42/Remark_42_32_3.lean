module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.VectorBundle
public import stacks_project.Chap42.Remark_42_32_8

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Remark 42.32.3 (1): if `X` is a vector bundle of rank `r` over `Y`, then the pullback
map `CH_k(Y) → CH_{k + r}(X)` is an isomorphism. -/
@[stacks 02TU] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.flatPullback_bijective :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℰ : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r ℰ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
      [Scheme.IsRelativeSpectrumOver P] (k : ℤ),
      -- Local instance justification (proof-local temporary data): the named local-finite-type proof is installed only within this closed Prop result because flatPullback consumes this class.
      letI : LocallyOfFiniteType
          (Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom)).hom :=
        Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X ℰ P
      -- Local instance justification (proof-local temporary data): the named flatness proof is installed only within this closed Prop result because flatPullback consumes this class.
      letI : Flat
          (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℰ P) :
            Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X)) :=
        Scheme.AssociatedVectorBundle.overHomFlat X ℰ P
      -- Local instance justification (proof-local temporary data): the named relative-dimension proof is installed only within this closed Prop result because flatPullback consumes this class.
      letI : Scheme.Hom.RelativeDimension
          (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ ℰ P) :
            Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X)) r :=
        Scheme.AssociatedVectorBundle.overHomRelativeDimension X ℰ r P
      Function.Bijective
        (AlgebraicGeometry.ChowGroup.flatPullback δ
          (Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom)) X
          (Over.homMk (Scheme.associatedVectorBundleπ ℰ P) rfl :
            Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X)
          r k))

/- Remark 42.32.3 (2): the same pullback is an isomorphism whenever `X ⟶ Y` satisfies
the local-𝔸^r hypotheses of Lemma 42.32.1. -/
@[stacks 02TU] #check
  (AlgebraicGeometry.ChowGroup.flatPullback_bijective_of_localAffineSpace :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
        Nonempty (Over.mk (f.left ∣_ U) ≅
          Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
      (k : ℤ),
      Function.Bijective (AlgebraicGeometry.ChowGroup.flatPullback δ X Y f r k))
