/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Order
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

/- The source-facing datum is exactly `TopologicalSpace.induced`. The canonical theorems
`continuous_iff_le_induced`, `isOpen_induced_iff`, and `isClosed_induced_iff` give its
weakest-continuity, open-set, and closed-set views. They hold for every map. The source's
injectivity setup is therefore retained by tagged `#check` specializations, rather than by
competing wrapper declarations. `Topology.IsInducing.induced` and `Topology.IsEmbedding.induced`
instead package properties of the resulting map. -/

/- The primitive owner object for the topology induced by a map `f` is the canonical topology
`TopologicalSpace.induced`. -/
@[stacks 09R8 "induced topology"]
#check TopologicalSpace.induced

/- Canonical order characterization of the induced topology. -/
#check continuous_iff_le_induced

/- Canonical open-set characterization of the induced topology. -/
#check isOpen_induced_iff

/- Canonical closed-set characterization of the induced topology. -/
#check isClosed_induced_iff

universe u v

variable {X : Type u} {Y : Type v} [tX : TopologicalSpace X]

/- Lemma 5.6.1 (1), tag 09R8: the source's injective-map specialization of the canonical
weakest-topology characterization. -/
@[stacks 09R8 "weakest topology making the injective map continuous"]
#check fun {f : Y → X} (_ : f.Injective) {t : TopologicalSpace Y} ↦
  @continuous_iff_le_induced Y X f t tX

/- Lemma 5.6.1 (2), tag 09R8: the source's injective-map specialization of the canonical
open-set characterization. -/
@[stacks 09R8 "open subsets of the induced topology as preimages"]
#check fun {f : Y → X} (_ : f.Injective) {s : Set Y} ↦
  @isOpen_induced_iff Y X tX s f

/- Lemma 5.6.1 (3), tag 09R8: the source's injective-map specialization of the canonical
closed-set characterization. -/
@[stacks 09R8 "closed subsets of the induced topology as preimages"]
#check fun {f : Y → X} (_ : f.Injective) {s : Set Y} ↦
  @isClosed_induced_iff Y X tX s f
