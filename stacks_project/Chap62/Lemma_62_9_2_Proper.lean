/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Proper

/-!
# Proper families of cycles on fibres

This file records the Stacks condition that the support of a family of
`r`-cycles on fibres is contained in a closed subset proper over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

open Scheme.Hom.CyclesOnFibers

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.Proper :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ},
    Scheme.Hom.CyclesOnFibers f r → Prop)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.proper_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : Scheme.Hom.CyclesOnFibers f r),
    Proper α ↔ ∃ W : TopologicalSpace.Closeds X,
      support α ⊆ W ∧ ClosedSubset.IsProperOver f W)

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.proper_of_subset :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : Scheme.Hom.CyclesOnFibers f r) (W : TopologicalSpace.Closeds X),
    support α ⊆ W → ClosedSubset.IsProperOver f W → Proper α)
