/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product.Counterexample

/-!
# The affine line over `ℚ(i)` as a `ℚ`-scheme

This file constructs the affine line over the quadratic extension
`ratSqrtNegOne` of `ℚ` and records that it is an integral 1-dimensional
finite-type `ℚ`-scheme whose base change along `Spec ℂ ⟶ Spec ℚ` is not
integral.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RatSqrtNegOneAffineLine

/-- The coordinate ring of the affine line over `ratSqrtNegOne`. -/
abbrev CoordinateRing : Type :=
  Polynomial ratSqrtNegOne

/-- The affine line over `ℚ(i)`. -/
def scheme : Scheme :=
  Spec (CommRingCat.of CoordinateRing)

/-- The structure morphism from the affine line over `ℚ(i)` to `Spec ℚ`. -/
def toSpecRat : scheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ CoordinateRing))

/-- The fiber product of `scheme` with `Spec ℂ` over `Spec ℚ`. -/
def complexBaseChange : Scheme :=
  FieldExtension.baseChange ℚ ℂ toSpecRat

/-- The coordinate ring `ℚ(i)[t]` is an integral domain. -/
instance instIsDomainCoordinateRing : IsDomain CoordinateRing := sorry

/-- The affine line over `ℚ(i)` is an integral scheme. -/
instance instIsIntegralScheme : IsIntegral scheme :=
  (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of CoordinateRing)).2
    instIsDomainCoordinateRing

/-- The affine line over `ℚ(i)` is 1-dimensional. -/
theorem topologicalKrullDim_eq_one : topologicalKrullDim scheme = 1 := sorry

/-- The structure morphism `toSpecRat` is of finite type. -/
instance instFiniteTypeToSpecRat : Scheme.Hom.FiniteType toSpecRat := sorry

/-- The complex fiber product is not an integral scheme. -/
theorem not_isIntegral_complexBaseChange : ¬ IsIntegral complexBaseChange := sorry

end AlgebraicGeometry.RatSqrtNegOneAffineLine
