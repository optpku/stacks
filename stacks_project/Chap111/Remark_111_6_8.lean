module

import ReasLib.Topology.Compactness.Hausdorff
import StacksCheckRecall

universe u

/- Remark 111.6.8: Unlike mathlib's separation-free `CompactSpace`, the word compact is
reserved for spaces that are both quasi-compact and Hausdorff. -/
@[stacks 02D3]
#check (TopologicalSpace.IsCompactHausdorff : (X : Type u) → [TopologicalSpace X] → Prop)
