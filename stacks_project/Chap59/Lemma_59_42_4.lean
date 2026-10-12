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

noncomputable section

universe u w

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.42.4 (1): for an integral or separated locally quasi-finite morphism,
the small abelian direct-image counit is epic on every sheaf. -/
@[stacks 04C9] #check
  (AlgebraicGeometry.SmallAbelianPushforward.counit_epi (f := f) :
    (IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) →
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
        Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
          AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F))

/- Lemma 59.42.4 (2): for an integral or separated locally quasi-finite morphism,
the small abelian direct image is faithful. -/
@[stacks 04C9] #check
  (AlgebraicGeometry.SmallAbelianPushforward.faithful (f := f) :
    (IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) →
      (smallAbelianPushforward f).Faithful)

/- Lemma 59.42.4 (3): for an integral or separated locally quasi-finite morphism,
the small abelian direct image reflects monomorphisms. -/
@[stacks 04C9] #check
  (AlgebraicGeometry.SmallAbelianPushforward.reflectsMonomorphisms (f := f) :
    (IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) →
      (smallAbelianPushforward f).ReflectsMonomorphisms)

/- Lemma 59.42.4 (4): for an integral or separated locally quasi-finite morphism,
the small abelian direct image reflects epimorphisms. -/
@[stacks 04C9] #check
  (AlgebraicGeometry.SmallAbelianPushforward.reflectsEpimorphisms (f := f) :
    (IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) →
      (smallAbelianPushforward f).ReflectsEpimorphisms)
