module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.Lemma_110_4_1_System

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopCat.Counterexample.NatQuasiCompact

/-- Lemma 110.4.1: there exists an inverse system of quasi-compact topological spaces
over ℕ whose limit is not quasi-compact. -/
@[stacks 09ZK]
theorem exists_compactSpace_limit_not_compactSpace :
    ∃ F : ℕᵒᵖ ⥤ TopCat.{0},
      (∀ n, CompactSpace (F.obj n)) ∧ ¬ CompactSpace (limit F : TopCat) :=
  sorry

end TopCat.Counterexample.NatQuasiCompact
