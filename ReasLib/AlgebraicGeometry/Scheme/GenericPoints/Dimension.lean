/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A point of a scheme is a generic point precisely when its local ring has Krull dimension zero. -/
theorem mem_genericPoints_iff_ringKrullDim_stalk_eq_zero {X : Scheme.{u}} (x : X) :
    x ∈ genericPoints X ↔ ringKrullDim (X.presheaf.stalk x) = 0 := sorry

/-- The generic points of the one-dimensional irreducible components of a scheme. -/
noncomputable def oneDimensionalGenericPoints (X : Scheme.{u}) : Set X :=
  {η | ∃ Z : irreducibleComponents X,
    topologicalKrullDim (X.irreducibleComponentSubscheme Z) = 1 ∧
      IsGenericPoint η (Z : Set X)}

/-- A point belongs to `oneDimensionalGenericPoints X` exactly when it is generic for an
irreducible component of `X` whose reduced component subscheme has dimension one. -/
theorem mem_oneDimensionalGenericPoints {X : Scheme.{u}} (η : X) :
    η ∈ oneDimensionalGenericPoints X ↔
      ∃ Z : irreducibleComponents X,
        topologicalKrullDim (X.irreducibleComponentSubscheme Z) = 1 ∧
          IsGenericPoint η (Z : Set X) := sorry

end AlgebraicGeometry.Scheme
