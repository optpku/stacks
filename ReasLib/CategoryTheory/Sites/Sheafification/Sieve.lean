module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Sheafification of sieve inclusions

This leaf connects a covering sieve with the weak-equivalence condition on
its canonical inclusion into a representable presheaf.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Sieve

variable {C : Type u} [Category.{v} C] {U : C}

/-- Lemma 7.50.1 (00ZO): a sieve is covering exactly when its canonical inclusion into the
representable presheaf is a weak equivalence after sheafification. -/
@[stacks 00ZO]
theorem mem_iff_W_functorInclusion
    (J : GrothendieckTopology C) (S : Sieve U)
    [J.PreservesSheafification
      (CategoryTheory.uliftFunctor.{u, v} : Type v ⥤ Type (max u v))] :
    S ∈ J U ↔ J.W S.functorInclusion := sorry

end CategoryTheory.Sieve
