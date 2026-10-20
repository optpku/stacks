module

public import ReasLib.Topology.Sheaves.Basis.Stalks
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u v

namespace BasisSheaf

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}
variable (F : BasisSheaf.{u, max u v} B) (hB : Opens.IsBasis B)
variable (U : BasisOpen B)

/- Lemma 6.30.5: for a sheaf of sets `F` on a topological basis `B` and `U ∈ B`, taking germs
identifies sections on `U` with the families of stalk elements that are locally represented by a
section on some basis neighborhood inside `U` at every point. -/
@[stacks 009M]
#check sections_bijOn_locallyRepresentableFamilies F hB U

end BasisSheaf
