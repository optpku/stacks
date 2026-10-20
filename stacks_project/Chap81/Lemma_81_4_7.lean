/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Modification
import StacksCheckRecall

/-!
# Lemma 81.4.7

Glueing Type-valued sheaves on the small étale site of an algebraic space along
a proper morphism that is an isomorphism off a closed subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

universe u

/- Lemma 81.4.7: Let `S` be a scheme. Let `f : Y' ⟶ Y` be a proper morphism of
algebraic spaces over `S`. Let `i : Z ⟶ Y` be a closed immersion. If `E` is
cartesian over `Y` via `j : E ⟶ Y'` and `g : E ⟶ Z`, and `f` is an isomorphism
over `Y \ Z`, then `glueFunctor f i j g h_cart` is an equivalence
`Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
CategoricalPullback (pullback j) (pullback g)`. -/
@[stacks 0GFY] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.glueFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i],
    IsIsoOverOpen f (closedImmersionComplementι i) →
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.glueFunctor f i j g h_cart).IsEquivalence)

/- If `E` is the chosen fibre product `Z ×_Y Y'`, then `glueFunctor` is an
equivalence. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.glueFunctor_isEquivalence_of_hasPullback :
    ∀ {S : Scheme.{u}} {Y' Y Z : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) [Proper f] [IsClosedImmersion i],
    IsIsoOverOpen f (closedImmersionComplementι i) →
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.glueFunctor f i
        (Limits.pullback.snd i f) (Limits.pullback.fst i f)
        (IsPullback.of_hasPullback i f).flip).IsEquivalence)
