/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinal-bounded Brown representability sets

This file packages the two Brown-set conditions for the sublevel set of an object-size
function.  It is independent of how a particular category defines the size of its objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace CategoryTheory.BrownRepresentability.Bounded

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- Objects whose value under `size` is at most `kappa`. -/
@[stacks 0GYG "cardinal-bounded object set"]
def objects (size : D → Cardinal.{w}) (kappa : Cardinal.{w}) : Set D :=
  fun X ↦ size X ≤ kappa

/-- The bounded objects detect every nonzero object by a nonzero incoming morphism. -/
def DetectsNonzeroObjects (size : D → Cardinal.{w}) (kappa : Cardinal.{w}) : Prop :=
  ∀ X : D, ¬ IsZero X →
    ∃ E : D, E ∈ objects size kappa ∧ ∃ f : E ⟶ X, f ≠ 0

/-- Every map from a bounded object into a countable coproduct factors through a countable
coproduct of bounded objects, component by component. -/
def FactorsThroughCountableCoproducts
    (size : D → Cardinal.{w}) (kappa : Cardinal.{w}) : Prop :=
  ∀ ⦃E : D⦄, E ∈ objects size kappa →
    ∀ (X : ℕ → D) [HasCoproduct X] (alpha : E ⟶ ∐ X),
      ∃ (E' : ℕ → D) (_ : HasCoproduct E')
        (phi : ∀ n : ℕ, E' n ⟶ X n) (beta : E ⟶ ∐ E'),
        (∀ n : ℕ, E' n ∈ objects size kappa) ∧
          alpha = beta ≫ Limits.Sigma.map phi

/-- The detecting and countable-factorization conditions make a bounded sublevel set a
Brown-representability set. -/
@[stacks 0GYG "bounded Brown-set criterion"]
theorem isSet [HasCountableCoproducts D]
    (size : D → Cardinal.{w}) (kappa : Cardinal.{w})
    (hdetect : DetectsNonzeroObjects size kappa)
    (hfactor : FactorsThroughCountableCoproducts size kappa) :
    BrownRepresentability.IsSet (objects size kappa) := sorry

end CategoryTheory.BrownRepresentability.Bounded
