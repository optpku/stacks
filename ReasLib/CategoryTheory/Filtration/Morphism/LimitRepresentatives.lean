/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives

/-!
# Explicit Limit Representatives of Filtered Morphisms

This module separates the data of eventual cycle and boundary representatives from the
complete-lattice construction of their canonical choices.  It is therefore available to any
downstream convergence argument that supplies extremal representatives explicitly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredObject C}

/-- Explicit eventual boundary and cycle representatives of a filtered morphism, together with
their universal extremal properties.  Cycles live in the source and boundaries live in the
target, so this owner applies to arbitrary filtered morphisms rather than only endomorphisms. -/
@[stacks 012I "explicit limit representatives of a filtered morphism"]
structure LimitRepresentatives (f : X ⟶ Y) where
  /-- The eventual boundary representative at a filtration index. -/
  boundary : ℤ → Subobject Y.obj
  /-- The eventual cycle representative at a filtration index. -/
  cycle : ℤ → Subobject X.obj
  /-- The eventual boundary is the least upper bound of all finite boundary representatives. -/
  boundary_isLUB (p : ℤ) :
    IsLUB (Set.range fun r : ℕ ↦ f.boundaryRepresentative r p) (boundary p)
  /-- The eventual cycle is the greatest lower bound of all finite cycle representatives. -/
  cycle_isGLB (p : ℤ) :
    IsGLB (Set.range fun r : ℕ ↦ f.cycleRepresentative r p) (cycle p)

namespace LimitRepresentatives

variable {f : X ⟶ Y}

/-- Every finite boundary representative is contained in the selected eventual boundary. -/
@[stacks 012I "finite boundary stage into an explicit limit representative"]
theorem boundary_stage_le (L : LimitRepresentatives f) (p : ℤ) (r : ℕ) :
    f.boundaryRepresentative r p ≤ L.boundary p := sorry

/-- The selected eventual boundary is below every common upper bound of finite boundary
representatives. -/
@[stacks 012I "leastness of an explicit boundary limit representative"]
theorem boundary_least (L : LimitRepresentatives f) (p : ℤ) (B : Subobject Y.obj)
    (hB : ∀ r : ℕ, f.boundaryRepresentative r p ≤ B) :
    L.boundary p ≤ B := sorry

/-- The selected eventual cycle is contained in every finite cycle representative. -/
@[stacks 012I "explicit limit representative into a finite cycle stage"]
theorem cycle_le_stage (L : LimitRepresentatives f) (p : ℤ) (r : ℕ) :
    L.cycle p ≤ f.cycleRepresentative r p := sorry

/-- Every common lower bound of finite cycle representatives is below the selected eventual
cycle. -/
@[stacks 012I "greatestness of an explicit cycle limit representative"]
theorem cycle_greatest (L : LimitRepresentatives f) (p : ℤ) (Z : Subobject X.obj)
    (hZ : ∀ r : ℕ, Z ≤ f.cycleRepresentative r p) :
    Z ≤ L.cycle p := sorry

/-- Eventual boundary representatives are independent of the chosen explicit limit package. -/
@[stacks 012I "uniqueness of an eventual boundary representative"]
theorem boundary_eq (L L' : LimitRepresentatives f) (p : ℤ) :
    L.boundary p = L'.boundary p := sorry

/-- Eventual cycle representatives are independent of the chosen explicit limit package. -/
@[stacks 012I "uniqueness of an eventual cycle representative"]
theorem cycle_eq (L L' : LimitRepresentatives f) (p : ℤ) :
    L.cycle p = L'.cycle p := sorry

/-- Explicit limit-representative packages are unique.  Their boundary and cycle data are
unique by the universal properties, and their remaining fields are propositions. -/
@[stacks 012I "uniqueness of explicit limit representatives"]
theorem eq (L L' : LimitRepresentatives f) : L = L' := sorry

section Canonical

/-- The canonical eventual boundary is the supremum of its finite boundary representatives. -/
@[stacks 012I "canonical eventual boundary as a least upper bound"]
theorem eventualBoundaryRepresentative_isLUB
    [LocallySmall.{v} C] [WellPowered.{v} C] [HasCoproducts.{v} C]
    (f : X ⟶ Y) (p : ℤ) :
    IsLUB (Set.range fun r : ℕ ↦ f.boundaryRepresentative r p)
      (f.eventualBoundaryRepresentative p) := sorry

/-- The canonical eventual cycle is the infimum of its finite cycle representatives. -/
@[stacks 012I "canonical eventual cycle as a greatest lower bound"]
theorem eventualCycleRepresentative_isGLB
    [LocallySmall.{v} C] [WellPowered.{v} C] [HasWidePullbacks.{v} C]
    (f : X ⟶ Y) (p : ℤ) :
    IsGLB (Set.range fun r : ℕ ↦ f.cycleRepresentative r p)
      (f.eventualCycleRepresentative p) := sorry

variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/-- The canonical subobject meets and joins provide the package of eventual representatives. -/
@[stacks 012I "canonical explicit limit representatives of a filtered morphism"]
noncomputable def canonical (f : X ⟶ Y) : LimitRepresentatives f where
  boundary := fun p ↦ f.eventualBoundaryRepresentative p
  cycle := fun p ↦ f.eventualCycleRepresentative p
  boundary_isLUB := eventualBoundaryRepresentative_isLUB f
  cycle_isGLB := eventualCycleRepresentative_isGLB f

/-- The boundary component of the canonical limit-representative package is the existing
supremum-defined representative. -/
@[simp, stacks 012I "canonical boundary limit representative"]
theorem canonical_boundary (f : X ⟶ Y) (p : ℤ) :
    (canonical f).boundary p = f.eventualBoundaryRepresentative p := sorry

/-- The cycle component of the canonical limit-representative package is the existing
infimum-defined representative. -/
@[simp, stacks 012I "canonical cycle limit representative"]
theorem canonical_cycle (f : X ⟶ Y) (p : ℤ) :
    (canonical f).cycle p = f.eventualCycleRepresentative p := sorry

end Canonical

end LimitRepresentatives

end FilteredObject.Hom
end CategoryTheory
