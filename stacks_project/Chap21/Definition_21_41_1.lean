/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial
import StacksCheckRecall

/-!
# Definition 21.41.1

The reusable owners for the simplicial site, its associated ring sheaf, and its module category
live in `CategoryTheory.SimplicialSite`.  This chapter file is only the source-facing recall.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory SimplicialSite

namespace CategoryTheory.SimplicialSite

/- Definition 21.41.1: for a site `(C, J)` and
`A : SimplicialObject (Sheaf J CommRingCat)`, a simplicial `A`-module is a sheaf of modules over
the associated ring sheaf `ringSheaf A` on the product site with object category
`SimplexCategory × C` and coverings fixed in the simplex coordinate.  The declarations below are
the projection, topology, associated ring sheaf, module category, and unit module implementing
that statement. -/
@[stacks 09D1 "Definition 21.41.1 projection"]
#check @projection

@[stacks 09D1 "Definition 21.41.1 topology"]
#check @topology

@[stacks 09D1 "Definition 21.41.1 precoverage"]
#check @precoverage

@[stacks 09D1 "Definition 21.41.1 covering membership"]
#check @Precoverage.mem_onSnd_iff

@[stacks 09D1 "Definition 21.41.1 inherited-topology bridge"]
#check @topology_eq_inherited

@[stacks 09D1 "Definition 21.41.1 presheaf functor"]
#check @presheafFunctor

@[stacks 09D1 "Definition 21.41.1 sheaf functor"]
#check @sheafFunctor

/- Definition 21.41.1: uncurrying a simplicial sheaf to the simplicial site. -/
@[stacks 09D1 "Definition 21.41.1 ring sheaf"]
#check @ringPresheaf

@[stacks 09D1 "Definition 21.41.1 ring presheaf functor"]
#check @ringPresheafFunctor

@[stacks 09D1 "Definition 21.41.1 ring presheaf map"]
#check @ringPresheafMap

@[stacks 09D1 "Definition 21.41.1 associated sheaf"]
#check @ringSheaf

@[stacks 09D1 "Definition 21.41.1 associated sheaf functor"]
#check @ringSheafFunctor

@[stacks 09D1 "Definition 21.41.1 associated sheaf map"]
#check @ringSheafMap

@[stacks 09D1 "Definition 21.41.1 associated sheaf underlying map"]
#check @ringSheaf_val

@[stacks 09D1 "Definition 21.41.1 associated sheaf map underlying map"]
#check @ringSheafMap_val

@[stacks 09D1 "Definition 21.41.1 module category"]
#check @ModuleCat

@[stacks 09D1 "Definition 21.41.1 unit module"]
#check @unitModule

end CategoryTheory.SimplicialSite
