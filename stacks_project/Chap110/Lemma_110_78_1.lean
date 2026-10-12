/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Algebra.Group.SequentialColimitCounterexample
import StacksCheckRecall

/- Lemma 110.78.1: there exists a system `G₁ → G₂ → G₃ → ⋯` of abelian topological
groups such that `colim G_n` taken in the category of topological spaces is different
from `colim G_n` taken in the category of topological groups. The system is `system`,
with stages `G_{n+1} = ℚ × ℝ^{n+1}` and closed embeddings padding a trailing zero, and
the two colimits are compared as topologies on the algebraic sequential colimit
`colimitCarrier`. -/
@[stacks 0B2Z] #check
  (TopCat.Counterexample.NatAddGroupColimit.spaceColimitTopology_ne_groupColimitTopology :
    TopCat.Counterexample.NatAddGroupColimit.spaceColimitTopology ≠
      TopCat.Counterexample.NatAddGroupColimit.groupColimitTopology.toTopologicalSpace)
