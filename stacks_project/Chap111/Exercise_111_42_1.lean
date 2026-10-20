module

public import ReasLib.Topology.Sheaves.Cohomology.Real
import StacksCheckRecall

@[expose] public section

/- Exercise 111.42.1: on `X = ℝ` with the Euclidean topology, there exists an abelian sheaf
`F` with nonzero `H¹(X, F)`. The intended argument uses only functoriality of cohomology and
the long exact cohomology sequence. -/
@[stacks 0D8Q] #check (CategoryTheory.Sheaf.existsRealNonzeroFirstCohomology :
  ∃ F : (TopCat.of ℝ).Sheaf AddCommGrpCat.{0},
    ¬ CategoryTheory.Limits.IsZero
      (F.H' 1 (⊤ : TopologicalSpace.Opens (TopCat.of ℝ))))
