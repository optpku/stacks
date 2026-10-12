/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.GDelta.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nowhere-dense fibers of finite-type morphisms

This file relates nowhere density in the generic fiber to nowhere density in the fibers over an
open subscheme of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If a closed subset has nowhere-dense trace on the generic fiber of a finite-type morphism to
an irreducible scheme, then its trace is nowhere dense on every fiber over some nonempty open
subscheme of the target. -/
@[stacks 054X]
theorem exists_open_isNowhereDense_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (Z : Set X) (hZ : IsClosed Z)
    (hη : IsNowhereDense ((f.fiberι (genericPoint Y)) ⁻¹' Z)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V → IsNowhereDense ((f.fiberι y) ⁻¹' Z) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
