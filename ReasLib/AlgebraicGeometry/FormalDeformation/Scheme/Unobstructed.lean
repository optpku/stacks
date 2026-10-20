/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Unobstructed deformations of curves with isolated complete-intersection singularities
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))

/-- A separated finite-type local complete-intersection scheme over a field, of dimension
at most one and with finite nonsmooth locus, has an unobstructed deformation category. -/
theorem isUnobstructed_deformationCategory
    [Scheme.Hom.FiniteType hX] [IsSeparated hX] [Syntomic hX]
    (hdim : topologicalKrullDim X ≤ 1)
    (hns : {x : X | ¬ Scheme.Hom.SmoothAt hX x}.Finite) :
    Functor.IsUnobstructed (deformationForget Λ k X hX) := sorry

/-- Deformations of a separated finite-type local complete-intersection scheme of dimension
at most one with finite nonsmooth locus are unobstructed. -/
instance instIsUnobstructed_deformationCategory
    [Scheme.Hom.FiniteType hX] [IsSeparated hX] [Syntomic hX]
    [hdim : Fact (topologicalKrullDim X ≤ 1)]
    [hns : Fact ({x : X | ¬ Scheme.Hom.SmoothAt hX x}.Finite)] :
    Functor.IsUnobstructed (deformationForget Λ k X hX) :=
  isUnobstructed_deformationCategory Λ k X hX hdim.out hns.out

end FlatSchemeCat
