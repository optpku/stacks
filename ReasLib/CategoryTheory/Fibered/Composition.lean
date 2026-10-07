module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian

/-!
# Composition of fibered functors

Fibered functors are closed under composition.  The explicit theorem is convenient when
constructing bundled data, while the instance makes the same fact available to typeclass search.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/-- Lemma 4.33.12 (Stacks 09WV): the composite of two fibered functors is fibered. -/
@[stacks 09WV]
theorem IsFibered.compFunctor
    (F : A ⥤ B) (G : B ⥤ C) [F.IsFibered] [G.IsFibered] :
    (F ⋙ G).IsFibered := sorry

/-- Fiberedness of functors is available under composition through typeclass search. -/
instance isFibered_comp
    (F : A ⥤ B) (G : B ⥤ C) [F.IsFibered] [G.IsFibered] :
    (F ⋙ G).IsFibered := sorry

end CategoryTheory.Functor
