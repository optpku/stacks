/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint.Specialization
public import ReasLib.Topology.Specialization.Dimension
public import Mathlib.Topology.KrullDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Immediate specialization chains in scheme-theoretic fibres

For a locally finite-type morphism, the residue-field transcendence degree of a point
controls the length of an avoidant chain of immediate specializations in its fibre.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The closure of a point in its scheme-theoretic fibre has topological Krull dimension
equal to the transcendence degree of its residue field over the residue field of its image. -/
@[stacks 053V]
theorem topologicalKrullDim_closure_asFiber_eq_residueFieldTrdegAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) =
      (f.residueFieldTrdegAt x : WithBot ℕ∞) := sorry

/-- Given a specialization to a point closed in its fibre, there is a chain of immediate
specializations in the original fibre from the given point to a closed point specializing to
the target. The chain may be chosen to avoid any closed subset not containing its first point. -/
@[stacks 053V]
theorem exists_immediateSpecializationChain_avoiding
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X)
    (hxx' : Specializes x x')
    (hx'_closed : f.asFiber x' ∈ closedPoints (f.fiber (f x')))
    (Z : Set (f.fiber (f x))) (hZ : IsClosed Z)
    (hxZ : f.asFiber x ∉ Z) :
    ∃ chain : Fin (f.residueFieldTrdegAt x + 1) → f.fiber (f x),
      chain 0 = f.asFiber x ∧
        (∀ i : Fin (f.residueFieldTrdegAt x),
          IsImmediateSpecialization (chain i.castSucc) (chain i.succ)) ∧
        chain (Fin.last (f.residueFieldTrdegAt x)) ∈
          closedPoints (f.fiber (f x)) ∧
          Specializes (f.fiberι (f x) (chain (Fin.last (f.residueFieldTrdegAt x)))) x' ∧
          ∀ i : Fin (f.residueFieldTrdegAt x + 1), chain i ∉ Z := sorry

end AlgebraicGeometry.Scheme.Hom
