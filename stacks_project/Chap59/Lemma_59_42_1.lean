/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyA
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

/- Lemma 59.42.1 (1): under Property (A), small direct image reflects injections. -/
@[stacks 04DK] #check
  (AlgebraicGeometry.smallAbelianPushforward_reflectsMonomorphisms :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P],
      hasPropertyA f → (smallAbelianPushforward f).ReflectsMonomorphisms)

/- Lemma 59.42.1 (2): under Property (A), small direct image reflects surjections. -/
@[stacks 04DK] #check
  (AlgebraicGeometry.smallAbelianPushforward_reflectsEpimorphisms :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P],
      hasPropertyA f → (smallAbelianPushforward f).ReflectsEpimorphisms)

/- Lemma 59.42.1 (3): under Property (A), the counit is surjective on every abelian sheaf. -/
@[stacks 04DK] #check
  (AlgebraicGeometry.smallAbelianPushforward_counit_epi :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P],
      hasPropertyA f →
        ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
          Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
            AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F))

/- Lemma 59.42.1 (4): under Property (A), small direct image is faithful. -/
@[stacks 04DK] #check
  (AlgebraicGeometry.smallAbelianPushforward_faithful :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
      [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P],
      hasPropertyA f → (smallAbelianPushforward f).Faithful)
