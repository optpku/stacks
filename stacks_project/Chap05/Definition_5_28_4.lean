module

public import Mathlib.Topology.LocallyFinite
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.28.4: a family `E : I → Set X` is locally finite if every point has an open
neighbourhood meeting only finitely many sets `E i`; this is the canonical mathlib predicate
`LocallyFinite`. Its neighbourhood formulation specializes to open neighbourhoods via
`LocallyFinite.exists_mem_basis` and `nhds_basis_opens`. -/
@[stacks 0BDS "locally finite families of subsets"]
#check LocallyFinite
