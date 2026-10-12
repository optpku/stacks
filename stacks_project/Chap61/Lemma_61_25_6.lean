/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Topology.Constructible
public import stacks_project.Chap61.Lemma_61_17_2_Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.25.6

Exactness of the small pro-étale abelian direct image along a closed immersion
of schemes whose complement is a retrocompact open.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.25.6: if `i : Z ⟶ X` is a closed immersion of schemes and
`(Set.range i)ᶜ` is a retrocompact open of `X`, then
`smallPushforward i` is an exact functor
`Sheaf (topology Z) AddCommGrpCat ⥤ Sheaf (topology X) AddCommGrpCat`. -/
@[stacks 09BM]
theorem smallPushforward_exact_of_isRetrocompact_compl
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (h : IsRetrocompact (Set.range i)ᶜ)
    [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward i) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
