/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.flat :
  ∀ {X : Scheme.{u}} (ℰ : X.Modules) [Scheme.Modules.IsFiniteLocallyFree ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    Flat (Scheme.associatedVectorBundleπ ℰ P))

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.locallyOfFiniteType :
  ∀ {X : Scheme.{u}} (ℰ : X.Modules) [Scheme.Modules.IsFiniteLocallyFree ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    LocallyOfFiniteType (Scheme.associatedVectorBundleπ ℰ P))

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.relativeDimension :
  ∀ {X : Scheme.{u}} (ℰ : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    Scheme.Hom.RelativeDimension (Scheme.associatedVectorBundleπ ℰ P) r)

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp :
  ∀ {S : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom]
    (ℰ : X.left.Modules) [Scheme.Modules.IsFiniteLocallyFree ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    LocallyOfFiniteType (Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom)).hom)

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.overHomFlat :
  ∀ {S : Scheme.{u}} (X : Over S)
    (ℰ : X.left.Modules) [Scheme.Modules.IsFiniteLocallyFree ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    Flat ((Over.homMk (Scheme.associatedVectorBundleπ ℰ P) :
      Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X).left))

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.overHomRelativeDimension :
  ∀ {S : Scheme.{u}} (X : Over S) (ℰ : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    Scheme.Hom.RelativeDimension
      ((Over.homMk (Scheme.associatedVectorBundleπ ℰ P) :
        Over.mk (Scheme.associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X).left) r)

#check (AlgebraicGeometry.Scheme.AssociatedVectorBundle.localAffineSpace :
  ∀ {X : Scheme.{u}} (ℰ : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℰ))
    [Scheme.IsRelativeSpectrumOver P],
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Over.mk (Scheme.associatedVectorBundleπ ℰ P ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
