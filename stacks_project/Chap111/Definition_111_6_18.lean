module

import ReasLib.Topology.IrreducibleComponents.Membership
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 111.6.18: a maximal irreducible subset of a topological space `X` is
an irreducible component of `X`, and every such component is automatically closed.
The membership characterization is `TopologicalSpace.mem_irreducibleComponents_iff`. -/
@[stacks 027G]
#check (TopologicalSpace.mem_irreducibleComponents_iff :
  ∀ {X : Type u} [TopologicalSpace X] (s : Set X),
    s ∈ irreducibleComponents X ↔ Maximal IsIrreducible s)

/- Closedness companion: every irreducible component is closed. -/
#check (isClosed_of_mem_irreducibleComponents :
  ∀ {X : Type u} [TopologicalSpace X] (s : Set X),
    s ∈ irreducibleComponents X → IsClosed s)
