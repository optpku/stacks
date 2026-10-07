module

public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.FiberClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.NowhereDenseFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible components of fibres of finite-type morphisms

This file relates the numbers of irreducible components of fibres over nonempty open subsets of
the target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- Over some nonempty open subset of an irreducible base, the fibres of a finite-type morphism
have at least as many irreducible components as its generic fibre. -/
@[stacks 0554]
theorem exists_open_le_natCard_irreducibleComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ}
    (hη : Nat.card (irreducibleComponents (f.fiber (genericPoint Y))) = n) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
      n ≤ Nat.card (irreducibleComponents (f.fiber y)) := sorry

/-- For a finite-type morphism, the geometric irreducible-fibre component count is constant on a
nonempty open subset of the reduced closure of any point of the target. -/
@[stacks 055A]
theorem exists_open_geometricIrreducibleFiberComponentCount_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] (y : Y) :
    ∃ V : (PointClosure.scheme y).Opens, Nonempty V ∧
      ∃ c : ℕ∞, ∀ z : PointClosure.scheme y, z ∈ V →
        f.geometricIrreducibleFiberComponentCount (PointClosure.ι y z) = c := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
