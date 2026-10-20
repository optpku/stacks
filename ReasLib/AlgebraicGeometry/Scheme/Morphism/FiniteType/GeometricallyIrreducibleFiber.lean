/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Geometrically irreducible fibers of finite-type morphisms

This file relates geometric irreducibility of the generic fiber to geometric irreducibility
over a nonempty open subset of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If the generic fiber of a finite-type morphism to an irreducible scheme is geometrically
irreducible, then the morphism is geometrically irreducible over some nonempty open subscheme. -/
theorem exists_open_geometricallyIrreducible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint Y))] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
