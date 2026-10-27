/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Action.ModuleCat.Concrete

/-!
# Linear actions with open stabilizers

A discrete module carries a continuous action of a topological group exactly when every element
has open stabilizer.  Since `ModuleCat R` has no canonical forgetful functor to `TopCat`, the
open-stabilizer condition is the intrinsic owner for this category; `DiscreteContAction` from
Mathlib is not directly applicable.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Topology

universe u v

namespace CategoryTheory.Action.ModuleCat

variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The property that every element of an `R`-linear `G`-action has open stabilizer. -/
@[stacks 04JF "open-stabilizer property"]
def openStabilizer : ObjectProperty (Action (ModuleCat.{max u v} R) G) :=
  fun X ↦ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)

/-- The category of discrete `R`-modules equipped with a continuous `G`-action, modeled by the
equivalent intrinsic open-stabilizer condition. -/
@[stacks 04JF "category of discrete continuous module actions"]
abbrev DiscreteModuleCat := (openStabilizer R G).FullSubcategory

namespace OpenStabilizer

/-- Membership in `openStabilizer` is the pointwise open-stabilizer condition. -/
theorem mem_iff (X : Action (ModuleCat.{max u v} R) G) :
    openStabilizer R G X ↔ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G) := sorry

/-- On a discrete topology, the open-stabilizer condition is equivalent to continuity of the
action.  The topology is an explicit view because `ModuleCat R` does not own one canonically. -/
theorem continuousSMul_iff (X : Action (ModuleCat.{max u v} R) G)
    [TopologicalSpace X.V] [DiscreteTopology X.V] :
    ContinuousSMul G X.V ↔ openStabilizer R G X := sorry

/-- The open-stabilizer property contains a zero object. -/
instance containsZero : (openStabilizer R G).ContainsZero where
  exists_zero := by
    let Z : Action (ModuleCat.{max u v} R) G :=
      Action.trivial G (ModuleCat.of R PUnit.{max u v + 1})
    letI : Subsingleton Z.V := inferInstanceAs (Subsingleton PUnit.{max u v + 1})
    refine ⟨Z, ?_, ?_⟩
    · show IsZero Z
      apply (IsZero.iff_id_eq_zero Z).2
      apply Action.hom_injective
      exact (ModuleCat.isZero_of_subsingleton Z.V).eq_of_src _ _
    · show openStabilizer R G Z
      intro x
      have h : (MulAction.stabilizer G x : Set G) = Set.univ :=
        Set.eq_univ_of_forall fun g ↦
          MulAction.mem_stabilizer_iff.2 (Subsingleton.elim _ _)
      rw [h]
      exact isOpen_univ

/-- The open-stabilizer property is stable under subobjects. -/
instance closedUnderSubobjects : (openStabilizer R G).IsClosedUnderSubobjects := sorry

/-- For a topological group, the open-stabilizer property is stable under quotient objects:
the stabilizer of a quotient element contains the open stabilizer of any lift. -/
instance closedUnderQuotients [IsTopologicalGroup G] :
    (openStabilizer R G).IsClosedUnderQuotients := sorry

/-- The open-stabilizer property is stable under finite products. -/
instance closedUnderFiniteProducts :
    (openStabilizer R G).IsClosedUnderFiniteProducts := sorry

/-- The inclusion of discrete continuous module actions preserves monomorphisms. -/
instance inclusionPreservesMonomorphisms :
    (openStabilizer R G).ι.PreservesMonomorphisms := sorry

end OpenStabilizer

end CategoryTheory.Action.ModuleCat
