/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-
Lemma 21.4.3 (03AJ): for an abelian sheaf `H` on a site, the canonical map from
`Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups H)` to `H.H 1` is bijective.

The reusable owner keeps the representative-level cokernel extension explicit; only its
exactness, independence of representatives, and the classification theorem are deferred.
-/
@[stacks 03AJ "torsor class map"] #check
  @Sheaf.Torsor.Cohomology.classMap

@[stacks 03AJ "torsors classified by first cohomology"] #check
  @Sheaf.Torsor.Cohomology.classMap_bijective

#check @Sheaf.Torsor.Cohomology.classMap_apply
#check @Sheaf.Torsor.Cohomology.classMap_trivial
#check @Sheaf.Torsor.Cohomology.extension

end
