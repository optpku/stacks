/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.FiniteRefinement
import StacksCheckRecall

@[expose] public section

/- Lemma 7.17.2 [0D05]: finite-refinement and finite-subcover properties belong to the neutral
chosen-cover and Grothendieck-topology APIs.  The canonical all-arrows family of a presieve is
`Presieve.ofArrows_uncurry_eq`. -/
@[stacks 0D05 "the all-arrows family generates its presieve"] #check @CategoryTheory.Presieve.ofArrows_uncurry_eq

@[stacks 0D05 "finite refinements of chosen covers"] #check @CategoryTheory.Precoverage.HasFiniteRefinement

@[stacks 0D05 "finite subcovers of chosen covers"] #check @CategoryTheory.Precoverage.HasFiniteSubcover

@[stacks 0D05 "finite subcovers imply finite refinements"] #check @CategoryTheory.Precoverage.HasFiniteSubcover.toFiniteRefinement

@[stacks 0D05 "finite refinements of covering sieves"] #check @CategoryTheory.GrothendieckTopology.HasFiniteRefinement

@[stacks 0D05 "finite subcovers of covering sieves"] #check @CategoryTheory.GrothendieckTopology.HasFiniteSubcover

@[stacks 0D05 "sieve-saturated finite subcovers imply finite refinements"] #check @CategoryTheory.GrothendieckTopology.HasFiniteSubcover.toFiniteRefinement
