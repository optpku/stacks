module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.ReflectsIsomorphisms.Evaluation

/-!
# Detecting exactness by additive Yoneda functors

This file records the two endpoint-sensitive Yoneda criteria for a short complex in an abelian
category.  The statements use the canonical `ShortComplex.Exact`, `Mono`, and `Epi` predicates.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.ShortComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- 05AA (Lemma 12.5.8 (1)): exactness together with an epimorphic final map is detected by all
contravariant additive representable functors. -/
@[stacks 05AA]
theorem exact_and_epi_iff_yoneda (S : ShortComplex A) :
    (S.Exact ∧ Epi S.g) ↔
      ∀ N : A,
        (S.op.map (preadditiveYoneda.obj N)).Exact ∧
          Mono (S.op.map (preadditiveYoneda.obj N)).f := sorry

/-- 05AA (Lemma 12.5.8 (2)): exactness together with a monomorphic initial map is detected by all
covariant additive representable functors. -/
@[stacks 05AA]
theorem exact_and_mono_iff_coyoneda (S : ShortComplex A) :
    (S.Exact ∧ Mono S.f) ↔
      ∀ N : A,
        (S.map (preadditiveCoyoneda.obj (Opposite.op N))).Exact ∧
          Mono (S.map (preadditiveCoyoneda.obj (Opposite.op N))).f := sorry

end CategoryTheory.ShortComplex
