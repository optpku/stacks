/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.VectorBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.36.3: for the rank-`r` vector bundle associated to a finite locally free module on
`X`, flat pullback is a bijection from `CH_k(X)` to `CH_(k + r)` of the total space. -/
@[stacks 02TY] #check
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
