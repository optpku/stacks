/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.AutEmbedding
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

universe u v w

namespace CategoryTheory

namespace Aut

/-- Automorphisms of a type carry the topology of pointwise convergence on
the discrete underlying type. -/
instance typeTopologicalSpace (X : Type w) : TopologicalSpace (Aut X) :=
  ⨅ x : X, TopologicalSpace.induced (fun automorphism : Aut X ↦ automorphism.hom x) ⊥

/-- Automorphisms of a discrete type form a topological group for the topology
of pointwise convergence. -/
instance typeIsTopologicalGroup (X : Type w) : IsTopologicalGroup (Aut X) := sorry

end Aut

namespace Functor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- Natural automorphisms carry the topology induced by their components in
the product of the objectwise pointwise-convergence automorphism groups. -/
instance autTopologicalSpace : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autEmbedding F) inferInstance

/-- Taking components identifies the natural automorphisms of a type-valued
functor with a closed subgroup of the product of its objectwise automorphism groups. -/
theorem autEmbedding_isClosedEmbedding :
    Topology.IsClosedEmbedding (autEmbedding F) := sorry

/-- Natural automorphisms of a type-valued functor form a topological group
for the topology of pointwise convergence on all objects and elements. -/
instance autIsTopologicalGroup : IsTopologicalGroup (Aut F) := sorry

/-- The pointwise-convergence topology on natural automorphisms of a
type-valued functor is totally disconnected. -/
instance autTotallyDisconnectedSpace : TotallyDisconnectedSpace (Aut F) := sorry

/-- Natural automorphisms of a functor with finite fibers form a compact
space for the topology of pointwise convergence. -/
instance autCompactSpace [∀ object : C, Finite (F.obj object)] :
    CompactSpace (Aut F) := sorry

end Functor

end CategoryTheory
