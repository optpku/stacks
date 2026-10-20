/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber

/-!
# Geometrically reduced fibers of finite-type morphisms

This file relates geometric reducedness, or its failure, of the generic fiber to the
corresponding behavior over a nonempty open subset of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If the generic fiber of a finite-type morphism to an irreducible scheme is not geometrically
reduced, then every fiber over some nonempty open subset is not geometrically reduced. -/
@[stacks 0577]
theorem exists_open_not_geometricallyReduced_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (hη : ¬ GeometricallyReduced (f.fiberToSpecResidueField (genericPoint Y))) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V → ¬ GeometricallyReduced (f.fiberToSpecResidueField y) := sorry

/-- If the generic fiber of a finite-type morphism to an irreducible scheme is geometrically
reduced, then the morphism is geometrically reduced over some nonempty open subscheme. -/
@[stacks 0578]
theorem exists_open_geometricallyReduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    [GeometricallyReduced (f.fiberToSpecResidueField (genericPoint Y))] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyReduced (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
