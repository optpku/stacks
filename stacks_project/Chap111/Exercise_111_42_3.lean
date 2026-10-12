/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Cohomology.FiniteSpace
import StacksCheckRecall

@[expose] public section

/- Exercise 111.42.3 (1): let `X` be a topological space. If `X` has two or fewer
points, then the global sheaf cohomology `F.H' i ⊤` is zero for every abelian sheaf
`F` and every positive degree `i`. -/
@[stacks 0D8S] #check
  (CategoryTheory.Sheaf.isZero_higherCohomology_of_enatCard_le_two :
    ∀ (X : TopCat) (hX : ENat.card X ≤ 2) (F : X.Sheaf AddCommGrpCat)
      (i : ℕ), 0 < i → CategoryTheory.Limits.IsZero
        (F.H' i (⊤ : TopologicalSpace.Opens X)))

/- Exercise 111.42.3 (2): the vanishing in (1) need not hold when `X` has three
points: there exist a three-point space and an abelian sheaf `F` with nonzero
`F.H' 1 ⊤`. -/
@[stacks 0D8S] #check
  (CategoryTheory.Sheaf.exists_threePoint_abelianSheaf_nonzero_firstCohomology :
    ∃ (X : TopCat) (F : X.Sheaf AddCommGrpCat),
      ENat.card X = 3 ∧ ¬ CategoryTheory.Limits.IsZero
        (F.H' 1 (⊤ : TopologicalSpace.Opens X)))
