/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.AffineBundle
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

/-!
# Flat pullback along finite locally free vector bundles

This file records homotopy invariance of Chow groups for the relative-spectrum model of a
finite locally free vector bundle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.AssociatedVectorBundle

/-- Flat pullback along the projection of the vector bundle associated to a finite locally free
module of rank `r` is a bijection from `CH_k` of the base to `CH_(k + r)` of the total space. -/
theorem flatPullback_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℰ : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P] (k : ℤ) :
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
      (flatPullback δ (Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom)) X
        (Over.homMk (Scheme.associatedVectorBundleπ ℰ P) :
          Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X)
        r k) := sorry

end AlgebraicGeometry.ChowGroup.AssociatedVectorBundle
