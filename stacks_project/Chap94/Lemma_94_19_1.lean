module

public import stacks_project.Chap94.Lemma_94_19_1_Localization
public import stacks_project.Chap94.Lemma_94_19_1_OverSlice

/-!
# Lemma 94.19.1

Constructions A and B of Stacks Section 8.13 restrict to inverse isomorphisms
of 2-categories between algebraic stacks over `S` and pairs consisting of an
algebraic stack over `S'` with a morphism to `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStacks

/-- Lemma 94.19.1: let `Sch_fppf` be a big fppf site, and let `g : S ⟶ S'` be a
morphism of this site. Constructions A and B of Stacks Section 8.13 give inverse
isomorphisms of 2-categories between `AlgebraicStacks S` and `OverSlice g`, the
2-category of pairs `(X', f)` consisting of an algebraic stack `X'` over `S'`
and a morphism `f : X' ⟶ overSlice g` of algebraic stacks over `S'`. -/
@[stacks 04X5]
theorem toOverSlice.isStrictInverse {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctor.IsStrictInverse (toOverSlice g) (ofOverSlice g) :=
  sorry

end AlgebraicGeometry.AlgebraicStacks
