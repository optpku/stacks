module

public import stacks_project.Chap67.Lemma_67_13_5_Adjunction
public import stacks_project.Chap67.Lemma_67_13_5_Complement

/-!
# Lemma 67.13.5

Small étale pushforward along a closed immersion of algebraic spaces is fully
faithful on sheaves of sets and on abelian sheaves, with essential image the
sheaves restricting to `*` off `Z` and the abelian sheaves supported on `|Z|`.
In both cases `i_small^{-1}` is a left inverse of `i_small,*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Lemma 67.13.5 (1): small étale pushforward of sheaves of sets along a closed
immersion of algebraic spaces is full. -/
@[stacks 04E5, instance]
theorem sheafPushforward_closedImmersion_type_full :
    (sheafPushforward (Type (u + 1)) i).Full := sorry

/-- Lemma 67.13.5 (2): small étale pushforward of sheaves of sets along a closed
immersion of algebraic spaces is faithful. -/
@[stacks 04E5, instance]
theorem sheafPushforward_closedImmersion_type_faithful :
    (sheafPushforward (Type (u + 1)) i).Faithful := sorry

/-- Lemma 67.13.5 (3): the essential image of small étale set-valued pushforward
along a closed immersion consists of sheaves whose restriction to `X \ Z` is isomorphic
to the terminal sheaf `*`. -/
@[stacks 04E5]
theorem mem_essImage_sheafPushforward_closedImmersion_type_iff
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafPushforward (Type (u + 1)) i).essImage F ↔
      restrictsToTerminalOnComplement i F := sorry

/-- Lemma 67.13.5 (4): small étale inverse image of sheaves of sets is a left inverse
of pushforward along a closed immersion, equivalently the adjunction counit is invertible. -/
@[stacks 04E5, instance]
theorem isIso_counit_sheafPushforward_closedImmersion_type
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) (Type (u + 1))] :
    IsIso (sheafAdjunction (Type (u + 1)) i).counit := sorry

/-- Lemma 67.13.5 (5): small étale pushforward of abelian sheaves along a closed
immersion of algebraic spaces is full. -/
@[stacks 04E5, instance]
theorem sheafPushforward_closedImmersion_ab_full :
    (sheafPushforward AddCommGrpCat.{u + 1} i).Full := sorry

/-- Lemma 67.13.5 (6): small étale pushforward of abelian sheaves along a closed
immersion of algebraic spaces is faithful. -/
@[stacks 04E5, instance]
theorem sheafPushforward_closedImmersion_ab_faithful :
    (sheafPushforward AddCommGrpCat.{u + 1} i).Faithful := sorry

/-- Lemma 67.13.5 (7): the essential image of small étale abelian pushforward along
a closed immersion consists of abelian sheaves whose support is contained in `|Z|`. -/
@[stacks 04E5]
theorem mem_essImage_sheafPushforward_closedImmersion_ab_iff
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj)) AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (sheafPushforward AddCommGrpCat.{u + 1} i).essImage F ↔
      supportSubsetImage i F := sorry

/-- Lemma 67.13.5 (8): small étale inverse image of abelian sheaves is a left inverse
of pushforward along a closed immersion, equivalently the adjunction counit is invertible. -/
@[stacks 04E5, instance]
theorem isIso_counit_sheafPushforward_closedImmersion_ab
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) AddCommGrpCat.{u + 1}] :
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} i).counit := sorry

end AlgebraicGeometry.AlgebraicSpace
