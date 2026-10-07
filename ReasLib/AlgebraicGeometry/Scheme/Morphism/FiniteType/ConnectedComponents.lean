module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ConnectedComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.FiberClosure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected components of fibres of finite-type morphisms

This file relates the number of connected components of the generic fibre to those of fibres over
a nonempty open subset of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- Over some nonempty open subset of an irreducible base, the fibres of a finite-type morphism
have at least as many connected components as its generic fibre. -/
@[stacks 055D]
theorem exists_open_le_natCard_connectedComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ}
    (hη : Nat.card (ConnectedComponents (f.fiber (genericPoint Y))) = n) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
      n ≤ Nat.card (ConnectedComponents (f.fiber y)) := sorry

/-- For a finite-type morphism, the number of geometric connected components of the fibre is
constant on a nonempty open subset of the reduced closure of any point of the target. -/
theorem exists_open_geometricFiberComponentCount_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] (y : Y) :
    ∃ V : (PointClosure.scheme y).Opens, Nonempty V ∧
      ∃ c : ℕ∞, ∀ z : PointClosure.scheme y, z ∈ V →
        f.geometricFiberComponentCount (PointClosure.ι y z) = c := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
