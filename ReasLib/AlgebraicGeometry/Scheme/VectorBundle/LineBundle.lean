/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic

/-!
# Vector bundles associated to invertible modules

This file records the geometric properties of the relative-spectrum model of the vector
bundle associated to an invertible module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The projection of the vector bundle associated to an invertible module is flat. -/
theorem associatedVectorBundleπ_flat {X : Scheme.{u}} (ℒ : X.Modules)
    [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P] :
    Flat (associatedVectorBundleπ ℒ P) := sorry

/-- The projection of the vector bundle associated to an invertible module has relative
dimension one. -/
theorem associatedVectorBundleπ_relativeDimension {X : Scheme.{u}} (ℒ : X.Modules)
    [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P] :
    Hom.RelativeDimension (associatedVectorBundleπ ℒ P) 1 := sorry

/-- The projection of the vector bundle associated to an invertible module is locally of
finite type. -/
theorem associatedVectorBundleπ_locallyOfFiniteType {X : Scheme.{u}} (ℒ : X.Modules)
    [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P] :
    LocallyOfFiniteType (associatedVectorBundleπ ℒ P) := sorry

/-- An invertible-module vector bundle is locally isomorphic over its base to relative affine
one-space. -/
theorem associatedVectorBundleπ_localAffineSpace {X : Scheme.{u}} (ℒ : X.Modules)
    [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P] :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Over.mk (associatedVectorBundleπ ℒ P ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin 1); U.toScheme) ↘ U.toScheme)) := sorry

/-- The associated vector bundle over a locally finite type object is locally of finite type over
the common base. -/
theorem associatedVectorBundleOver_locallyOfFiniteType {S : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P] :
    LocallyOfFiniteType (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom := sorry

/-- The morphism over the base induced by an associated vector-bundle projection is flat. -/
theorem associatedVectorBundleOverHom_flat {S : Scheme.{u}} (X : Over S)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P]
    (w : associatedVectorBundleπ ℒ P ≫ X.hom =
      (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom) :
    Flat (Over.Hom.left (Over.homMk (associatedVectorBundleπ ℒ P) w :
      Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) := sorry

/-- The morphism over the base induced by an associated vector-bundle projection has relative
dimension one. -/
theorem associatedVectorBundleOverHom_relativeDimension {S : Scheme.{u}} (X : Over S)
    (ℒ : X.left.Modules) [Modules.Invertible ℒ]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
    [IsRelativeSpectrumOver P]
    (w : associatedVectorBundleπ ℒ P ≫ X.hom =
      (Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)).hom) :
    Hom.RelativeDimension
      (Over.Hom.left (Over.homMk (associatedVectorBundleπ ℒ P) w :
        Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom) ⟶ X)) 1 := sorry

end AlgebraicGeometry.Scheme
