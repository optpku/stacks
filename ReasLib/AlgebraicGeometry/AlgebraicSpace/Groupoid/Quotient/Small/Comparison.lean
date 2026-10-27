/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell

/-! # The source–target cell of a small quotient stack -/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Source points followed by the point inclusion into the groupoid prestack. -/
private abbrev sourcePre := AlgebraicSpace.toGroupoids.map G.s.left ≫ atlasToPreQuotient G

/-- Target points followed by the point inclusion into the groupoid prestack. -/
private abbrev targetPre := AlgebraicSpace.toGroupoids.map G.t.left ≫ atlasToPreQuotient G

/-- The endpoint equations for the arrow represented by a point of the relation space. -/
private def sourceEndpoints : Prop :=
  ∀ x : G.R.left.toGroupoids.total,
    G.s.left.app (op x.unop.fst.unop) x.unop.snd =
        ((toFunctor (sourcePre G)).obj x).fiber ∧
      G.t.left.app (op x.unop.fst.unop) x.unop.snd =
        (G.groupoidPresheaf.map (𝟙 (op x.unop.fst.unop))).obj
          ((toFunctor (targetPre G)).obj x).fiber

/-- The endpoint equations for the inverse of the arrow represented by a relation point. -/
private def targetEndpoints : Prop :=
  ∀ x : G.R.left.toGroupoids.total,
    G.s.left.app (op x.unop.fst.unop)
        (G.i.left.app (op x.unop.fst.unop) x.unop.snd) =
        ((toFunctor (targetPre G)).obj x).fiber ∧
      G.t.left.app (op x.unop.fst.unop)
          (G.i.left.app (op x.unop.fst.unop) x.unop.snd) =
        (G.groupoidPresheaf.map (𝟙 (op x.unop.fst.unop))).obj
          ((toFunctor (sourcePre G)).obj x).fiber

/-- A relation point supplies the vertical arrow between its source and target points. -/
private def sourceComponent (h : sourceEndpoints G) (x : G.R.left.toGroupoids.total) :
    (toFunctor (sourcePre G)).obj x ⟶ (toFunctor (targetPre G)).obj x where
  base := 𝟙 x.unop.fst.unop
  fiber := FunctorPointHom.ofArrow x.unop.snd (h x).1 (h x).2

/-- Groupoid inversion supplies the reverse vertical arrow of a relation point. -/
private def targetComponent (h : targetEndpoints G) (x : G.R.left.toGroupoids.total) :
    (toFunctor (targetPre G)).obj x ⟶ (toFunctor (sourcePre G)).obj x where
  base := 𝟙 x.unop.fst.unop
  fiber := FunctorPointHom.ofArrow
    (G.i.left.app (op x.unop.fst.unop) x.unop.snd) (h x).1 (h x).2

/-- Relation points have the specified endpoints and their vertical arrows
are natural in the test scheme. -/
private theorem sourceTargetPre_laws :
    sourceEndpoints G ∧ ∀ h : sourceEndpoints G,
      (∀ {x y : G.R.left.toGroupoids.total} (a : x ⟶ y),
        (toFunctor (sourcePre G)).map a ≫ sourceComponent G h y =
          sourceComponent G h x ≫ (toFunctor (targetPre G)).map a) ∧
      (∀ x : G.R.left.toGroupoids.total,
        (preQuotient G).p.IsHomLift (𝟙 (G.R.left.toGroupoids.p.obj x))
          (sourceComponent G h x)) := sorry

/-- Inverse relation points have the specified endpoints and their vertical
arrows are natural in the test scheme. -/
private theorem sourceTargetPreInv_laws :
    targetEndpoints G ∧ ∀ h : targetEndpoints G,
      (∀ {x y : G.R.left.toGroupoids.total} (a : x ⟶ y),
        (toFunctor (targetPre G)).map a ≫ targetComponent G h y =
          targetComponent G h x ≫ (toFunctor (sourcePre G)).map a) ∧
      (∀ x : G.R.left.toGroupoids.total,
        (preQuotient G).p.IsHomLift (𝟙 (G.R.left.toGroupoids.p.obj x))
          (targetComponent G h x)) := sorry

/-- The universal relation point gives a cell from the source atlas map to
the target atlas map in the groupoid prestack. -/
private def sourceTargetPre : sourcePre G ⟶ targetPre G :=
  ofBasedNatTrans
    { app := sourceComponent G (sourceTargetPre_laws G).1
      naturality := fun {_ _} a ↦ ((sourceTargetPre_laws G).2 (sourceTargetPre_laws G).1).1 a
      isHomLift' := (sourceTargetPre_laws G).2 (sourceTargetPre_laws G).1 |>.2 }

/-- Groupoid inversion gives the reverse source–target cell in the prestack. -/
private def sourceTargetPreInv : targetPre G ⟶ sourcePre G :=
  ofBasedNatTrans
    { app := targetComponent G (sourceTargetPreInv_laws G).1
      naturality := fun {_ _} a ↦ ((sourceTargetPreInv_laws G).2 (sourceTargetPreInv_laws G).1).1 a
      isHomLift' := (sourceTargetPreInv_laws G).2 (sourceTargetPreInv_laws G).1 |>.2 }

/-- The cells furnished by a relation point and its inverse are mutually inverse. -/
private theorem sourceTargetIso_laws :
    sourceTargetPre G ≫ sourceTargetPreInv G = 𝟙 (sourcePre G) ∧
      sourceTargetPreInv G ≫ sourceTargetPre G = 𝟙 (targetPre G) := sorry

/-- The two atlas maps from the relation space to the quotient stack are
canonically 2-isomorphic, through the universal groupoid arrow. -/
def sourceTargetIso :
    AlgebraicSpace.toGroupoids.map G.s.left ≫ atlas G ≅
      AlgebraicSpace.toGroupoids.map G.t.left ≫ atlas G :=
  (α_ (AlgebraicSpace.toGroupoids.map G.s.left) (atlasToPreQuotient G)
      (stackificationHom G)).symm ≪≫
    Bicategory.whiskerRightIso
      { hom := sourceTargetPre G
        inv := sourceTargetPreInv G
        hom_inv_id := (sourceTargetIso_laws G).1
        inv_hom_id := (sourceTargetIso_laws G).2 }
      (stackificationHom G) ≪≫
    α_ (AlgebraicSpace.toGroupoids.map G.t.left) (atlasToPreQuotient G)
      (stackificationHom G)

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
