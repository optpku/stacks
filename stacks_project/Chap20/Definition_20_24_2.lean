module

public import ReasLib.Topology.OpenCover.LocallyFinite
import StacksCheckRecall

@[expose] public section

/- Definition 20.24.2: an open covering `X = ⋃ i, U i` is locally finite if every
point has an open neighbourhood meeting only finitely many members `U i`. This is
identified with `IsOpenCover U ∧ LocallyFinite (Opens.asSets U)` via
`TopologicalSpace.locallyFiniteCover_iff`. -/
@[stacks 02FS]
#check TopologicalSpace.locallyFiniteCover_iff
