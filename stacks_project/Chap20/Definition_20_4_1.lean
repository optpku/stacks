/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Torsor
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.Sheaf.Torsor

variable {X : TopCat.{u}}
variable {G : X.Sheaf GrpCat.{u}}

/- Definition 20.4.1 [02FO]: the canonical owner of a `G`-torsor is
`CategoryTheory.Sheaf.Torsor G`.  Its generic torsor data and the topological opens-site
local-section API are respectively provided by `ReasLib.CategoryTheory.Sites.Torsor` and
`ReasLib.Topology.Sheaf.Torsor`. -/
@[stacks 02FO]
#check (Torsor G)

/- Morphisms of `G`-torsors are the canonical equivariant sheaf morphisms. -/
#check (Torsor.Hom : Torsor G → Torsor G → Type _)

/- The trivial `G`-torsor is the regular left action of `G` on itself. -/
#check (trivial G : Torsor G)

/- Pointwise local nonemptiness is exposed by the neutral opens-site API. -/
#check exists_open_nhdsWithin_nonempty_sections
#check locally_nonempty

end CategoryTheory.Sheaf.Torsor
