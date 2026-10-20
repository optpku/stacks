/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlgebraBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

open AlgebraicGeometry.Scheme.AlgebraBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (A : CommRingCat.{u}) (B : I ⥤ CommRingCat.{u})
variable (σ : (Functor.const I).obj A ⟶ B)
variable {X : Scheme.{u}} (f : X ⟶ Scheme.Spec.obj (op A))
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (g : T ⟶ S),
    ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The inverse image of `F` on the base change at a stage algebra. -/
def stageSheaf (i : I) :
    Sheaf (stage A B σ f i).smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (projection A B σ f i)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (stage A B σ f i).smallEtaleTopology).obj F

variable [HasColimit B]
variable [HasSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u}]

/-- The inverse image of `F` on the colimit base change. -/
def limitSheaf :
    Sheaf (limit A B σ f).smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (limitProjection A B σ f)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (limit A B σ f).smallEtaleTopology).obj F

/-- Pulling a stage sheaf back along a stage transition identifies it with the later stage sheaf. -/
def transitionIso {i j : I} (hij : i ≤ j) :
    ((smallEtalePullback (transition A B σ f hij)).sheafPullback AddCommGrpCat.{u}
        (stage A B σ f i).smallEtaleTopology (stage A B σ f j).smallEtaleTopology).obj
      (stageSheaf A B σ f F i) ≅ stageSheaf A B σ f F j :=
  let siteIso :
      smallEtalePullback (projection A B σ f i) ⋙
          smallEtalePullback (transition A B σ f hij) ≅
        smallEtalePullback (transition A B σ f hij ≫ projection A B σ f i) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (transition A B σ f hij) (projection A B σ f i)).symm
  let siteIso' :
      smallEtalePullback (transition A B σ f hij ≫ projection A B σ f i) ≅
        smallEtalePullback (projection A B σ f j) :=
    eqToIso (congrArg smallEtalePullback (transition_projection A B σ f hij))
  (Adjunction.leftAdjointCompIso
    (smallEtaleSheafAdjunction (projection A B σ f i))
    (smallEtaleSheafAdjunction (transition A B σ f hij))
    (smallEtaleSheafAdjunction (projection A B σ f j))
    (Functor.sheafPushforwardContinuousComp' (siteIso ≪≫ siteIso') AddCommGrpCat
      X.smallEtaleTopology
      (stage A B σ f i).smallEtaleTopology
      (stage A B σ f j).smallEtaleTopology)).app F

/-- The stage inverse-image sheaf is the displayed étale pullback of `F`. -/
theorem stageSheaf_eq (i : I) :
    stageSheaf A B σ f F i =
      ((smallEtalePullback (projection A B σ f i)).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology (stage A B σ f i).smallEtaleTopology).obj F := sorry

/-- Pulling a stage sheaf back from the colimit base change identifies it with the limit sheaf. -/
def fromLimitIso (i : I) :
    ((smallEtalePullback (fromLimit A B σ f i)).sheafPullback AddCommGrpCat.{u}
        (stage A B σ f i).smallEtaleTopology (limit A B σ f).smallEtaleTopology).obj
      (stageSheaf A B σ f F i) ≅ limitSheaf A B σ f F :=
  let siteIso :
      smallEtalePullback (projection A B σ f i) ⋙
          smallEtalePullback (fromLimit A B σ f i) ≅
        smallEtalePullback (fromLimit A B σ f i ≫ projection A B σ f i) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (fromLimit A B σ f i) (projection A B σ f i)).symm
  let siteIso' :
      smallEtalePullback (fromLimit A B σ f i ≫ projection A B σ f i) ≅
        smallEtalePullback (limitProjection A B σ f) :=
    eqToIso (congrArg smallEtalePullback (fromLimit_projection A B σ f i))
  (Adjunction.leftAdjointCompIso
    (smallEtaleSheafAdjunction (projection A B σ f i))
    (smallEtaleSheafAdjunction (fromLimit A B σ f i))
    (smallEtaleSheafAdjunction (limitProjection A B σ f))
    (Functor.sheafPushforwardContinuousComp' (siteIso ≪≫ siteIso') AddCommGrpCat
      X.smallEtaleTopology
      (stage A B σ f i).smallEtaleTopology
      (limit A B σ f).smallEtaleTopology)).app F

end AlgebraicGeometry.Scheme.Etale.AlgebraBaseChange

end
