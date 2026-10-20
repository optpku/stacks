/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ClosedImmersion
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

@[expose] public section

universe u

/- Proposition 59.46.4: small-étale pushforward along a closed immersion is fully
faithful for sheaves of sets and abelian sheaves, with essential images characterized
by terminal restriction to the complement and support in the closed image,
respectively. Inverse image is a left inverse in both cases. -/
@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_closedImmersion_type_full :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      (Scheme.smallEtaleDirectImage.{u, u} i).Full)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_closedImmersion_type_faithful :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      (Scheme.smallEtaleDirectImage.{u, u} i).Faithful)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.mem_essImage_smallEtalePushforward_closedImmersion_type_iff :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u,
        (Scheme.smallEtalePullback (closedImmersionComplement i).ι).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (Type u)),
      (Scheme.smallEtaleDirectImage.{u, u} i).essImage F ↔
        restrictsToTerminalOnComplement i F)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_counit_smallEtalePushforward_closedImmersion_type :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasWeakSheafify Z.smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u, (Scheme.smallEtalePullback i).op.HasLeftKanExtension P],
      IsIso ((Scheme.smallEtalePullback i).sheafAdjunctionContinuous
        (Type u) X.smallEtaleTopology Z.smallEtaleTopology).counit)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_closedImmersion_ab_full :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
        AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).Full)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_closedImmersion_ab_faithful :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
        AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).Faithful)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.mem_essImage_smallEtalePushforward_closedImmersion_ab_iff :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      ((Scheme.smallEtalePullback i).sheafPushforwardContinuous
        AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).essImage F ↔
        abelianSheafSupport F ⊆ Set.range i.base)

@[stacks 04CA] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_counit_smallEtalePushforward_closedImmersion_ab :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (Scheme.smallEtalePullback i).op.HasLeftKanExtension P],
      IsIso ((Scheme.smallEtalePullback i).sheafAdjunctionContinuous
        AddCommGrpCat.{u} X.smallEtaleTopology Z.smallEtaleTopology).counit)

#check
  (AlgebraicGeometry.Scheme.Etale.restrictsToTerminalOnComplement_iff :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology (Type u)]
      [∀ P : X.Etaleᵒᵖ ⥤ Type u,
        (Scheme.smallEtalePullback (closedImmersionComplement i).ι).op.HasLeftKanExtension P]
      (F : Sheaf X.smallEtaleTopology (Type u)),
      restrictsToTerminalOnComplement i F ↔
        Nonempty
          (IsTerminal
            (((Scheme.smallEtalePullback (closedImmersionComplement i).ι).sheafPullback
                (Type u) X.smallEtaleTopology
                (closedImmersionComplement i).toScheme.smallEtaleTopology).obj F)))
