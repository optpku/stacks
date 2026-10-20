/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 67.13.5

Small étale pushforward along a closed immersion of algebraic spaces is fully
faithful on sheaves of sets and on abelian sheaves, with essential image the
sheaves restricting to `*` off `Z` and the abelian sheaves supported on `|Z|`.
In both cases `i_small^{-1}` is a left inverse of `i_small,*`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 67.13.5: small étale direct image along a closed immersion is fully faithful,
with the stated essential images and invertible canonical counits. -/
@[stacks 04E5]
#check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_closedImmersion_type_full :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (sheafPushforward (Type (u + 1)) i).Full)

#check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_closedImmersion_type_faithful :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (sheafPushforward (Type (u + 1)) i).Faithful)

#check (AlgebraicGeometry.AlgebraicSpace.mem_essImage_sheafPushforward_closedImmersion_type_iff :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    (sheafPushforward (Type (u + 1)) i).essImage F ↔
      restrictsToTerminalOnComplement i F)

#check (AlgebraicGeometry.AlgebraicSpace.isIso_counit_sheafPushforward_closedImmersion_type :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) (Type (u + 1))],
    IsIso (sheafAdjunction (Type (u + 1)) i).counit)

#check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_closedImmersion_ab_full :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (sheafPushforward AddCommGrpCat.{u + 1} i).Full)

#check (AlgebraicGeometry.AlgebraicSpace.sheafPushforward_closedImmersion_ab_faithful :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (sheafPushforward AddCommGrpCat.{u + 1} i).Faithful)

#check (AlgebraicGeometry.AlgebraicSpace.mem_essImage_sheafPushforward_closedImmersion_ab_iff :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj)) AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (sheafPushforward AddCommGrpCat.{u + 1} i).essImage F ↔
      supportSubsetImage i F)

#check (AlgebraicGeometry.AlgebraicSpace.isIso_counit_sheafPushforward_closedImmersion_ab :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange i).op.HasLeftKanExtension P]
    [HasWeakSheafify (spacesEtaleTopology Z) AddCommGrpCat.{u + 1}],
    IsIso (sheafAdjunction AddCommGrpCat.{u + 1} i).counit)
