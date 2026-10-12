/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Geometrically connected fibers of finite-type morphisms

This file relates geometric connectedness of the generic fiber to geometric connectedness
over a nonempty open subset of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If the generic fiber of a finite-type morphism to an irreducible scheme is geometrically
connected, then the morphism is geometrically connected over some nonempty open subscheme. -/
theorem exists_open_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    [GeometricallyConnected (f.fiberToSpecResidueField (genericPoint Y))] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyConnected (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
