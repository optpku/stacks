module

public import ReasLib.Topology.Sheaves.Basis.Types.Extension
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u v

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}
variable (F : BasisSheaf.{u, max u v} B) (hB : Opens.IsBasis B)

/- Lemma 6.30.6: a sheaf of sets on a topological basis extends to a sheaf on the whole space,
uniquely up to a unique isomorphism compatible with restriction maps. -/
@[stacks 009N]
#check existsExtensionUniqueUpToUniqueIso F hB

end BasisSheaf
