module

public import Mathlib.Order.Defs.Unbundled
public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.28.1: being formally homotopic is an equivalence relation on Hom-sets
in CompleteLocalAlgCat Λ k. -/
@[stacks 0DQB]
theorem FormallyHomotopic.equivalence {R S : CompleteLocalAlgCat Λ k} :
    _root_.Equivalence (FormallyHomotopic : (R ⟶ S) → (R ⟶ S) → Prop) := sorry

/-- Formal homotopy is reflexive. -/
@[refl]
theorem FormallyHomotopic.refl {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    FormallyHomotopic f f := sorry

/-- Formal homotopy is symmetric. -/
@[symm]
theorem FormallyHomotopic.symm {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S} :
    FormallyHomotopic f g → FormallyHomotopic g f := sorry

/-- Formal homotopy is transitive. -/
@[trans]
theorem FormallyHomotopic.trans {R S : CompleteLocalAlgCat Λ k} {f g h : R ⟶ S} :
    FormallyHomotopic f g → FormallyHomotopic g h → FormallyHomotopic f h := sorry

/-- Formal homotopy is an `IsEquiv` relation on each Hom-set of `CompleteLocalAlgCat`. -/
instance FormallyHomotopic.instIsEquiv {R S : CompleteLocalAlgCat Λ k} :
    IsEquiv (R ⟶ S) FormallyHomotopic := sorry

end CompleteLocalAlgCat
