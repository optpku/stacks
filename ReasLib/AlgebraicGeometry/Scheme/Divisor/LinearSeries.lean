/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearSubsystem
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSeries

open Scheme Scheme.IdealSheafData

/-- An effective Cartier divisor and a section subspace determine a linear series. -/
def ofDivisorSubspace
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    {d r : ℕ}
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ))
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (finrank_eq : Module.finrank k V = r + 1) :
    LinearSeries X (topologicalKrullDim_eq_one X).le d r :=
  ofSubmodule X (topologicalKrullDim_eq_one X).le d r
    D.associatedSheaf V degree_eq finrank_eq

/-- The divisor-subspace construction has line bundle `𝒪_X(D)` and section space `V`. -/
theorem ofDivisorSubspace_spec
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    {d r : ℕ}
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ))
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (finrank_eq : Module.finrank k V = r + 1) :
    (ofDivisorSubspace X D degree_eq V finrank_eq).lineBundle = D.associatedSheaf ∧
      (ofDivisorSubspace X D degree_eq V finrank_eq).sections = V := sorry

/-- The embedded projective subsystem attached to the constructed linear series is the one
induced by its specified section subspace `V`. -/
theorem ofDivisorSubspace_inclusion
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    {d r : ℕ}
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ))
    (V : Submodule k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))
    [FiniteDimensional k V] (finrank_eq : Module.finrank k V = r + 1) :
    LinearSubsystem.inclusion X D
        (ofDivisorSubspace X D degree_eq V finrank_eq).sections =
      LinearSubsystem.inclusion X D V := sorry

end AlgebraicGeometry.LinearSeries
