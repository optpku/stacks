module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.IntegralEmbedding
import StacksCheckRecall

/-!
# Lemma 67.53.7

Small étale pushforward along a universally injective integral morphism of algebraic
spaces is fully faithful on sheaves of sets and on abelian sheaves. Its essential image
is characterized by terminal restriction off the image, respectively support in the image.
In both cases inverse image is a left inverse of pushforward.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.53.7 (1): fullness for sheaves of sets. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_integralUnivInj_type_full :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f],
    (sheafPushforward (Type (u + 1)) f).Full)

/- Lemma 67.53.7 (2): faithfulness for sheaves of sets. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_integralUnivInj_type_faithful :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f],
    (sheafPushforward (Type (u + 1)) f).Faithful)

/- Lemma 67.53.7 (3): essential image for sheaves of sets. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.mem_essImage_sheafPushforward_integralUnivInj_type_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    (sheafPushforward (Type (u + 1)) f).essImage F ↔
      restrictsToTerminalOnImageComplement f F)

/- Lemma 67.53.7 (4): the left-inverse property for sheaves of sets. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.isIso_counit_sheafPushforward_integralUnivInj_type :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) (Type (u + 1))],
    IsIso (sheafAdjunction (Type (u + 1)) f).counit)

/- Lemma 67.53.7 (5): fullness for abelian sheaves. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_integralUnivInj_ab_full :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f],
    (sheafPushforward AddCommGrpCat.{u + 1} f).Full)

/- Lemma 67.53.7 (6): faithfulness for abelian sheaves. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_integralUnivInj_ab_faithful :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f],
    (sheafPushforward AddCommGrpCat.{u + 1} f).Faithful)

/- Lemma 67.53.7 (7): essential image for abelian sheaves. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.mem_essImage_sheafPushforward_integralUnivInj_ab_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (sheafPushforward AddCommGrpCat.{u + 1} f).essImage F ↔
      abelianSheafSupport F ⊆ pointsImage f)

/- Lemma 67.53.7 (8): the left-inverse property for abelian sheaves. -/
@[stacks 0AEH] #check (AlgebraicGeometry.AlgebraicSpace.isIso_counit_sheafPushforward_integralUnivInj_ab :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}],
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} f).counit)
