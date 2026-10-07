module

public import stacks_project.Chap59.Lemma_59_104_7_Glue
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleSheaf

universe u

/-- Lemma 59.104.7: if `f : X' ⟶ X` is proper, `i : Z ⟶ X` is a closed immersion,
`E` is cartesian over `X` via `j : E ⟶ X'` and `g : E ⟶ Z`, and `f` is an
isomorphism over `closedImmersionComplement i`, then `glueFunctor f i j g h_cart`
is an equivalence
`Sheaf X.smallEtaleTopology (Type (u+1)) ⥤ CategoricalPullback (pullback j) (pullback g)`. -/
@[stacks 0GF4]
theorem glueFunctor_isEquivalence {X X' Z E : Scheme.{u}}
    (f : X' ⟶ X) (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [IsProper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverComplement f i) :
    (glueFunctor f i j g h_cart).IsEquivalence := sorry
