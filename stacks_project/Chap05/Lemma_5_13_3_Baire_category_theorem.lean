module

public import Mathlib.Topology.Baire.LocallyCompactRegular
import StacksCheckRecall

@[expose] public section

open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/- Lemma 5.13.3 (Baire category theorem): in a locally quasi-compact Hausdorff
space, the intersection of a sequence of dense open subsets is dense. -/
@[stacks 0CQN]
#check fun {U : ℕ → Set X} (hU_open : ∀ n, IsOpen (U n)) (hU_dense : ∀ n, Dense (U n)) ↦
  dense_iInter_of_isOpen hU_open hU_dense
