/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.ULift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing directed orders and systems

This leaf transports the order-theoretic part of a directed diagram along an
explicit `OrderIso`.  The isomorphism is an argument rather than an instance:
there can be many presentations of the same index type, and registering all of
them globally would make typeclass search non-deterministic.
-/

@[expose] public section

universe u v w z

namespace OrderIso

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]

/-- An order isomorphism transports directedness from its codomain to its domain. -/
theorem isDirectedOrder (e : J ≃o I) [IsDirectedOrder I] :
    IsDirectedOrder J := sorry

end OrderIso

namespace ULift

variable {I : Type u} [Preorder I]

/-- `ULift` preserves directedness of a preorder. -/
@[instance]
theorem isDirectedOrder [IsDirectedOrder I] :
    IsDirectedOrder (ULift.{v} I) := sorry

end ULift

namespace DirectedSystem

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]
variable {F : I → Type w}

/-- The transition family obtained by pulling a directed system back along an
explicit order isomorphism `e : J ≃o I`. -/
def reindexMap (e : J ≃o I) (f : ∀ i j, i ≤ j → F i → F j) :
    ∀ j k : J, j ≤ k → F (e j) → F (e k) :=
  fun j k h => f (e j) (e k) (e.monotone h)

/-- Evaluation of the pulled-back transition family. -/
@[simp]
theorem reindexMap_apply (e : J ≃o I) (f : ∀ i j, i ≤ j → F i → F j)
    (j k : J) (h : j ≤ k) (x : F (e j)) :
    reindexMap e f j k h x = f (e j) (e k) (e.monotone h) x := sorry

/-- Reindexing along the identity order isomorphism leaves every transition
map unchanged. -/
@[simp]
theorem reindexMap_refl (f : ∀ i j, i ≤ j → F i → F j)
    (j k : I) (h : j ≤ k) (x : F j) :
    reindexMap (OrderIso.refl I) f j k h x = f j k h x := sorry

/-- Successive pullbacks of a transition family agree with the pullback along
the composite order isomorphism. -/
@[simp]
theorem reindexMap_trans {K : Type z} [Preorder K]
    (e : J ≃o I) (d : K ≃o J) (f : ∀ i j, i ≤ j → F i → F j)
    (k l : K) (h : k ≤ l) (x : F (e (d k))) :
    reindexMap d (reindexMap e f) k l h x =
      reindexMap (d.trans e) f k l h x := sorry

/-- Pull a `DirectedSystem` back along an explicit order isomorphism. -/
theorem reindex (e : J ≃o I) (f : ∀ i j, i ≤ j → F i → F j)
    [DirectedSystem F (fun i j h ↦ f i j h)] :
    DirectedSystem (fun j : J ↦ F (e j))
      (fun j k h ↦ reindexMap e f j k h) := sorry

/-- The canonical directed-system transport to a `ULift` of the index type. -/
theorem ulift (f : ∀ i j, i ≤ j → F i → F j)
    [DirectedSystem F (fun i j h ↦ f i j h)] :
    DirectedSystem (fun j : ULift.{v} I ↦ F j.down)
      (fun j k h ↦ f j.down k.down h) := sorry

end DirectedSystem
