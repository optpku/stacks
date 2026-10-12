/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_20_3_EtaleSupport
public import stacks_project.Chap67.Lemma_67_13_5_Adjunction
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap67.Lemma_67_53_7_ImageComplement

/-!
# Lemma 67.53.7

Small étale pushforward along a universally injective integral morphism of algebraic
spaces is fully faithful on sheaves of sets and on abelian sheaves, with essential image
the sheaves restricting to `*` off `f(|Y|)` and the abelian sheaves supported on
`f(|Y|)`. In both cases `f_small^{-1}` is a left inverse of `f_small,*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
variable [IsIntegralHom f] [UniversallyInjective f]

/-- Lemma 67.53.7 (1): small étale pushforward of sheaves of sets along a universally injective
integral morphism of algebraic spaces is full. -/
@[stacks 0AEH, instance]
theorem sheafPushforward_integralUnivInj_type_full :
    (sheafPushforward (Type (u + 1)) f).Full := sorry

/-- Lemma 67.53.7 (2): small étale pushforward of sheaves of sets along a universally injective
integral morphism of algebraic spaces is faithful. -/
@[stacks 0AEH, instance]
theorem sheafPushforward_integralUnivInj_type_faithful :
    (sheafPushforward (Type (u + 1)) f).Faithful := sorry

/-- Lemma 67.53.7 (3): the essential image of small étale set-valued pushforward along a
universally injective integral morphism consists of sheaves whose restriction to
`|X| \ f(|Y|)` is isomorphic to the terminal sheaf `*`. -/
@[stacks 0AEH]
theorem mem_essImage_sheafPushforward_integralUnivInj_type_iff
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafPushforward (Type (u + 1)) f).essImage F ↔
      restrictsToTerminalOnImageComplement f F := sorry

/-- Lemma 67.53.7 (4): small étale inverse image of sheaves of sets is a left inverse of
pushforward along a universally injective integral morphism, equivalently the adjunction
counit is invertible. -/
@[stacks 0AEH, instance]
theorem isIso_counit_sheafPushforward_integralUnivInj_type
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) (Type (u + 1))] :
    IsIso (sheafAdjunction (Type (u + 1)) f).counit := sorry

/-- Lemma 67.53.7 (5): small étale pushforward of abelian sheaves along a universally injective
integral morphism of algebraic spaces is full. -/
@[stacks 0AEH, instance]
theorem sheafPushforward_integralUnivInj_ab_full :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Full := sorry

/-- Lemma 67.53.7 (6): small étale pushforward of abelian sheaves along a universally injective
integral morphism of algebraic spaces is faithful. -/
@[stacks 0AEH, instance]
theorem sheafPushforward_integralUnivInj_ab_faithful :
    (sheafPushforward AddCommGrpCat.{u + 1} f).Faithful := sorry

/-- Lemma 67.53.7 (7): the essential image of small étale abelian pushforward along a
universally injective integral morphism consists of abelian sheaves on `X_étale` whose
support is contained in `f(|Y|)`. -/
@[stacks 0AEH]
theorem mem_essImage_sheafPushforward_integralUnivInj_ab_iff
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (sheafPushforward AddCommGrpCat.{u + 1} f).essImage F ↔
      abelianSheafSupport F ⊆ pointsImage f := sorry

/-- Lemma 67.53.7 (8): small étale inverse image of abelian sheaves is a left inverse of
pushforward along a universally injective integral morphism, equivalently the adjunction
counit is invertible. -/
@[stacks 0AEH, instance]
theorem isIso_counit_sheafPushforward_integralUnivInj_ab
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}] :
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} f).counit := sorry

end AlgebraicGeometry.AlgebraicSpace
