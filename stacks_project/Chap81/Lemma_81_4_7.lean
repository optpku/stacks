module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap81.Lemma_81_4_7_Glueing

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

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Lemma 81.4.7: Let `S` be a scheme. Let `f : Y' ⟶ Y` be a proper morphism of
algebraic spaces over `S`. Let `i : Z ⟶ Y` be a closed immersion. If `E` is
cartesian over `Y` via `j : E ⟶ Y'` and `g : E ⟶ Z`, and `f` is an isomorphism
over `Y \ Z`, then `glueFunctor f i j g h_cart` is an equivalence
`Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
CategoricalPullback (pullback j) (pullback g)`. -/
@[stacks 0GFY]
theorem glueFunctor_isEquivalence {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (glueFunctor f i j g h_cart).IsEquivalence :=
  sorry

/-- If `E` is the chosen fibre product `Z ×_Y Y'`, then `glueFunctor` is an
equivalence. -/
theorem glueFunctor_isEquivalence_of_hasPullback
    {S : Scheme.{u}} {Y' Y Z : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (glueFunctor f i (Limits.pullback.snd i f) (Limits.pullback.fst i f)
      (IsPullback.of_hasPullback i f).flip).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
