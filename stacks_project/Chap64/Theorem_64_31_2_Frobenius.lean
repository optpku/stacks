/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Frobenius
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField AlgebraicGeometry.Scheme.Etale
open CategoryTheory
universe u
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-! Compatibility checks for chapter names used by downstream source files. -/
#check (residueCard X : ∀ [Finite k] [LocallyOfFiniteType X.hom], closedPoints X.left → ℕ)
#check (geometricPointOverClosedPoint_spec X : ∀ v : closedPoints X.left,
  geometricPointOverClosedPoint X v =
    GeometricPoint.map
      (specFieldGeometricPoint (X.left.residueField v.1)
        (AlgebraicClosure (X.left.residueField v.1)))
      (X.left.fromSpecResidueField v.1))
#check (localGeometricFrobenius X : ∀ [Finite k] [ConnectedSpace X.left]
  [LocallyOfFiniteType X.hom] (v : closedPoints X.left),
  Aut (GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v)))
#check (etaleGeometricFrobenius X : ∀ [Finite k] [ConnectedSpace X.left]
  [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left) (v : closedPoints X.left),
  (GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅ GeometricPoint.finiteFiber xbar) →
    Aut (GeometricPoint.finiteFiber xbar))

end AlgebraicGeometry.SchemeOverField
