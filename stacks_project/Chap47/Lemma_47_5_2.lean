/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Existence
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.5.2: Every module over a ring admits an injective hull. -/
@[stacks 08Y3] #check (Module.exists_isInjectiveHull :
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    ∃ (I : Type (max u v)) (_ : AddCommGroup I) (_ : Module R I)
      (_ : Module.Injective R I) (f : M →ₗ[R] I), f.IsInjectiveHull)
