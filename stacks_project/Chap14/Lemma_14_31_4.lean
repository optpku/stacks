module

public import ReasLib.AlgebraicTopology.SimplicialSet.KanFibration.Limits
import StacksCheckRecall

/-!
@stack 08NX

# Lemma 14.31.4 compatibility facade

The countable-tower closure theorem is owned by ReasLib at the canonical `Fibration` layer for
every projection; the source statement is its initial-stage specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

variable {X : ℕ → SSet.{u}} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
variable [∀ n : ℕ, Fibration (f n)]

/- Lemma 14.31.4: the inverse-limit projection to the initial stage of a countable tower of Kan
fibrations is a Kan fibration. -/
@[stacks 08NX]
#check (SSet.modelCategoryQuillen.fibration.limitProjection f (i := 0) :
  Fibration (limit.π (Functor.ofOpSequence f) (Opposite.op 0)))
