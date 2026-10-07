module

public import Mathlib.Topology.Sheaves.Forget
import StacksCheckRecall

@[expose] public section

/- Lemma 6.9.2: composing a presheaf on a topological space with a limit-preserving
functor that reflects isomorphisms preserves and detects the sheaf condition. The canonical
theorem is stronger than the source only by allowing an arbitrary target category instead of
`Type`; its `Type` specialization is exactly the underlying-presheaf-of-sets statement. -/
@[stacks 0073 "sheaf condition detected by a limit-preserving functor"]
recall TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
