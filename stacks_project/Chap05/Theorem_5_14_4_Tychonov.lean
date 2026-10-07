module

public import Mathlib.Topology.Compactness.Compact
import StacksCheckRecall

@[expose] public section

universe u v

section

variable {ι : Type u} {X : ι → Type v}
variable [∀ i, TopologicalSpace (X i)]

/- Theorem 5.14.4 (Tychonov): if each factor `X i` is quasi-compact, then the product space
`∀ i, X i` is quasi-compact. Via Definition 5.12.1, quasi-compactness is `CompactSpace`, so this
is exactly the canonical product-space compactness instance `Pi.compactSpace`. -/
@[stacks 08ZU "arbitrary products of quasi-compact spaces are quasi-compact"]
#check Pi.compactSpace

end
