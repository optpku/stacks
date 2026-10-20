/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.DimensionZero

/-!
# Degrees of effective Cartier divisors on proper curves

This file relates the finite closed subscheme and associated invertible sheaf of an effective
Cartier divisor to curve degree.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Tensoring a finite locally free module of rank `n` with the associated sheaf of an effective
Cartier divisor preserves rank `n`. -/
instance tensorAssociatedSheaf_isFiniteLocallyFreeOfRank
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (ℰ : X.Modules) (n : ℕ) [Modules.IsFiniteLocallyFreeOfRank n ℰ] :
    Modules.IsFiniteLocallyFreeOfRank n (ℰ ⊗ D.associatedSheaf : X.Modules) := sorry

/-- An effective Cartier divisor on a proper scheme of topological Krull dimension at most one
over a field is finite over that field. -/
theorem subschemeIsFinite_of_isProper_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsFinite (D.subschemeι ≫ f) := sorry

/-- The curve degree of the invertible sheaf associated to an effective Cartier divisor equals
the dimension of the divisor's ring of global sections over the base field. -/
theorem curveDegreeOfInvertible_associatedSheaf_eq_finrank_globalSections
    {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hdim : topologicalKrullDim X ≤ 1) :
    Modules.curveDegreeOfInvertible f hdim D.associatedSheaf =
      (Module.finrank k (Scheme.Hom.globalSectionsAlg (D.subschemeι ≫ f)) : ℤ) := sorry

/-- Tensoring a rank-`n` finite locally free module by the associated sheaf of an effective
Cartier divisor adds `n` times the divisor's degree to its curve degree. -/
theorem curveDegree_tensor_associatedSheaf_eq
    {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hdim : topologicalKrullDim X ≤ 1)
    (ℰ : X.Modules) (n : ℕ) [Modules.IsFiniteLocallyFreeOfRank n ℰ] :
    Modules.curveDegree f hdim (ℰ ⊗ D.associatedSheaf : X.Modules) n =
      (n : ℤ) * Modules.curveDegreeOfInvertible f hdim D.associatedSheaf +
        Modules.curveDegree f hdim ℰ n := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
