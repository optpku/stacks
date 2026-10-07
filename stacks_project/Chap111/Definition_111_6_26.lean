module

public import ReasLib.Topology.ConnectedComponents.Basic
import StacksCheckRecall

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/- Definition 111.6.26: a connected component is a maximal connected subset,
equivalently the connected component of one of its points. -/
@[stacks 027I] #check (maximal_isConnected_iff_eq_connectedComponent :
  ∀ T : Set X, Maximal IsConnected T ↔ ∃ x : X, T = connectedComponent x)

/- A topological space is connected when it is nonempty and not the union of
two nonempty disjoint open subsets. -/
#check (ConnectedSpace X : Prop)

/- Space connectedness agrees with connectedness of the universal subset. -/
#check (connectedSpace_iff_univ : ConnectedSpace X ↔ IsConnected (Set.univ : Set X))

/- A preconnected set covered by two opens disjoint on it lies in one of them;
together with nonemptiness, this is the connectedness condition above. -/
#check (isPreconnected_iff_subset_of_disjoint : ∀ {T : Set X},
  IsPreconnected T ↔ ∀ U V : Set X, IsOpen U → IsOpen V →
    T ⊆ U ∪ V → T ∩ (U ∩ V) = ∅ → T ⊆ U ∨ T ⊆ V)

/- The canonical component construction is indexed by a point. -/
#check (connectedComponent : X → Set X)

/- Every point lies in its connected component. -/
#check (mem_connectedComponent : ∀ {x : X}, x ∈ connectedComponent x)

/- Every connected component is closed. -/
#check (isClosed_connectedComponent : ∀ {x : X}, IsClosed (connectedComponent x))

-- In general a connected component need not be open; `isOpen_connectedComponent`
-- requires `[LocallyConnectedSpace α]` and is not an unconditional fact.
