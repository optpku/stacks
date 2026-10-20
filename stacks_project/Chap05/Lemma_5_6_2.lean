module

public import Mathlib.Topology.Order
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

/- The source-facing datum is exactly `TopologicalSpace.coinduced`. The canonical theorems
`continuous_iff_coinduced_le`, `isOpen_coinduced`, and `isClosed_coinduced` give its
strongest-continuity, open-set, and closed-set views. They hold for every map. The source's
surjectivity setup is therefore retained by tagged `#check` specializations, rather than by
competing wrapper declarations. `Topology.IsCoinducing` and `Topology.IsQuotientMap` instead
package properties of a map between already topologized spaces. -/

/- The primitive owner object for the quotient topology associated to a map `f` is the canonical
coinduced topology `TopologicalSpace.coinduced`. -/
@[stacks 08ZK "quotient topology"]
#check TopologicalSpace.coinduced

/- Canonical order characterization of the coinduced topology. -/
#check continuous_iff_coinduced_le

/- Canonical open-set characterization of the coinduced topology. -/
#check isOpen_coinduced

/- Canonical closed-set characterization of the coinduced topology. -/
#check isClosed_coinduced

universe u v

variable {X : Type u} {Y : Type v} [tX : TopologicalSpace X]

/- Lemma 5.6.2 (1), tag 08ZK: the source's surjective-map specialization of the canonical
strongest-topology characterization. -/
@[stacks 08ZK "strongest topology making the surjective map continuous"]
#check fun {f : X → Y} (_ : f.Surjective) {t : TopologicalSpace Y} ↦
  @continuous_iff_coinduced_le X Y f tX t

/- Lemma 5.6.2 (2), tag 08ZK: the source's surjective-map specialization of the canonical
open-set characterization. -/
@[stacks 08ZK "open subsets of the quotient topology detected by preimage"]
#check fun {f : X → Y} (_ : f.Surjective) {s : Set Y} ↦
  @isOpen_coinduced X Y tX s f

/- Lemma 5.6.2 (3), tag 08ZK: the source's surjective-map specialization of the canonical
closed-set characterization. -/
@[stacks 08ZK "closed subsets of the quotient topology detected by preimage"]
#check fun {f : X → Y} (_ : f.Surjective) {s : Set Y} ↦
  @isClosed_coinduced X Y tX s f
