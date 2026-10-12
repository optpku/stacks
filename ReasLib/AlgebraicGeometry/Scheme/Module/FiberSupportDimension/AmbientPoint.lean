/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.Topology.KrullDimension.Local

/-!
# Fibre-support dimension at an ambient point

This module defines the local dimension of a fibrewise module support at an
arbitrary point of the ambient fibre.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The local dimension at `x` of the support of `F` on the fibre of `f` through `x`.
The neighbourhoods are taken in the ambient fibre, so the definition does not require
`x` to belong to the support. -/
noncomputable def ambientFiberSupportDimensionAt {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf (f.asFiber x),
    topologicalKrullDim
      (Set.inter (U : Set (f.fiber (f x)))
        (moduleSupport ((pullback (f.fiberι (f x))).obj F)))

/-- The ambient-point fibre-support dimension is computed from intersections with open
neighbourhoods in the ambient fibre. -/
theorem ambientFiberSupportDimensionAt_def {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) :
    ambientFiberSupportDimensionAt f F x =
      ⨅ U : OpenNhdsOf (f.asFiber x),
        topologicalKrullDim
          (Set.inter (U : Set (f.fiber (f x)))
            (moduleSupport ((pullback (f.fiberι (f x))).obj F))) := sorry

/-- At a point of the fibre support, ambient-point fibre-support dimension agrees with
the local dimension of the corresponding support point. -/
theorem ambientFiberSupportDimensionAt_eq_topologicalKrullDimAt {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (x : X)
    (supportPoint : moduleSupport ((pullback (f.fiberι (f x))).obj F))
    (supportPoint_eq : (supportPoint : f.fiber (f x)) = f.asFiber x) :
    ambientFiberSupportDimensionAt f F x = topologicalKrullDimAt supportPoint := sorry

end AlgebraicGeometry.Scheme.Modules
