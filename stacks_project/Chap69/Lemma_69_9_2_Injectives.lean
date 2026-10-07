module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Closed-immersion pushforward of injective abelian sheaves

The small étale abelian direct image along a closed immersion of algebraic spaces
preserves injective objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The small étale abelian direct image along a closed immersion of algebraic spaces
preserves injective objects. -/
instance sheafPushforward_preservesInjectiveObjects_of_isClosedImmersion
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    (sheafPushforward AddCommGrpCat.{u + 1} i).PreservesInjectiveObjects := sorry

end AlgebraicGeometry.AlgebraicSpace
