/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Exact
import StacksCheckRecall

@[expose] public section

universe u v

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/- Definition 111.2.8: an `R`-module `M` is of finite presentation over `R` when it is
`Module.FinitePresentation`, equivalently isomorphic to the cokernel of a map of finite
free modules `(Fin n → R) →ₗ[R] (Fin m → R)`. -/
@[stacks 0278] #check (Module.FinitePresentation.iff_exists_exact_free_sequence R M :
  Module.FinitePresentation R M ↔
    ∃ n m : ℕ, ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
      ∃ g : (Fin n → R) →ₗ[R] M, Function.Exact f g ∧ Function.Surjective g)

#check (Module.FinitePresentation R M : Prop)
