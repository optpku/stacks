/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.5

The source-facing map is owned by `TopologyComparison.Cohomology.edgeMap`: its coefficient is an
arbitrary sheaf in `A_X`, and its construction uses the exact inverse image and the adjunction
counit. The owner separates the site and morphism universes and exposes ordinary
`Sheaf.cohomologyOverObject` groups. This chapter file is intentionally a recall facade.
-/

open CategoryTheory

/- Lemma 21.30.5 (0EZC): under `(V_n)`, the map
`H^{n + 1}_{τ'}(X, ε_{X,*}F) ⟶ H^{n + 1}_τ(X, F)` is injective for `F ∈ A_X`, and its image is
the classes which become zero on a `τ'`-cover of `X`. -/
@[stacks 0EZC "(1)"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology.edgeMap_injective

@[stacks 0EZC "(2)"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology.mem_range_edgeMap_iff

@[stacks 0EZC "canonical map"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology.edgeMap

@[stacks 0EZC "canonical map naturality"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology.edgeMap_naturality

@[stacks 0EZC "functorial canonical map"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.Cohomology.edgeNatTrans

end
