/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/-- If a finite-type quasicoherent module has an impurity above a point, then it has one
whose base-change morphism is locally of finite presentation and whose special point is
closed in its scheme-theoretic fibre. -/
theorem exists_locallyOfFinitePresentation_closedPoint {X S : Scheme.{u}} (F : X.Modules)
    (f : X ⟶ S) [Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_impurity : Nonempty (Impurity F f s)) :
    ∃ I : Impurity F f s, LocallyOfFinitePresentation I.g ∧
      I.g.asFiber I.specialPoint ∈ closedPoints (I.g.fiber (I.g I.specialPoint)) := sorry

end AlgebraicGeometry.Scheme.Modules.Impurity
