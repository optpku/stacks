/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic

/-!
# Vector bundles associated to finite locally free modules

This file records geometric properties of the relative-spectrum model of the vector bundle
associated to a finite locally free module of constant rank.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedVectorBundle

/-- The projection of the vector bundle associated to a finite locally free module is flat. -/
theorem flat {X : Scheme.{u}} (ℰ : X.Modules) [Modules.IsFiniteLocallyFree ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    Flat (associatedVectorBundleπ ℰ P) := sorry

/-- The projection of the vector bundle associated to a finite locally free module is locally
of finite type. -/
theorem locallyOfFiniteType {X : Scheme.{u}} (ℰ : X.Modules)
    [Modules.IsFiniteLocallyFree ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    LocallyOfFiniteType (associatedVectorBundleπ ℰ P) := sorry

/-- The projection of the vector bundle associated to a finite locally free module of rank `r`
has relative dimension `r`. -/
theorem relativeDimension {X : Scheme.{u}} (ℰ : X.Modules) (r : ℕ)
    [Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    Hom.RelativeDimension (associatedVectorBundleπ ℰ P) r := sorry

/-- The total space of an associated vector bundle is locally of finite type over any base over
which the underlying scheme is locally of finite type. -/
theorem locallyOfFiniteTypeComp {S : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (ℰ : X.left.Modules) [Modules.IsFiniteLocallyFree ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    LocallyOfFiniteType (Over.mk (associatedVectorBundleπ ℰ P ≫ X.hom)).hom := sorry

/-- The morphism over the common base induced by an associated vector-bundle projection is
flat. -/
theorem overHomFlat {S : Scheme.{u}} (X : Over S)
    (ℰ : X.left.Modules) [Modules.IsFiniteLocallyFree ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    Flat ((Over.homMk (associatedVectorBundleπ ℰ P) :
      Over.mk (associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X).left) := sorry

/-- The morphism over the common base induced by a rank-`r` associated vector-bundle projection
has relative dimension `r`. -/
theorem overHomRelativeDimension {S : Scheme.{u}} (X : Over S)
    (ℰ : X.left.Modules) (r : ℕ) [Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    Hom.RelativeDimension
      ((Over.homMk (associatedVectorBundleπ ℰ P) :
        Over.mk (associatedVectorBundleπ ℰ P ≫ X.hom) ⟶ X).left) r := sorry

/-- A rank-`r` associated vector bundle is locally isomorphic over its base to relative affine
`r`-space. -/
theorem localAffineSpace {X : Scheme.{u}} (ℰ : X.Modules) (r : ℕ)
    [Modules.IsFiniteLocallyFreeOfRank r ℰ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℰ))
    [IsRelativeSpectrumOver P] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Over.mk (associatedVectorBundleπ ℰ P ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)) := sorry

end AlgebraicGeometry.Scheme.AssociatedVectorBundle
