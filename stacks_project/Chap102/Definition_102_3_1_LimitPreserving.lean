/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback

/-!
# Limit-preserving 1-morphisms of groupoid fibrations

The canonical comparison maps and the relative limit-preservation criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TypeCat
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open AlgebraicGeometry.Groupoids (homFunctor homCocone)
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.fiberHomFunctor :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : X.p.Fiber (D.obj i)),
    homFunctor x y ⟶
      homFunctor ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y))

#check (AlgebraicGeometry.Groupoids.Hom.fiberHomFunctor_app :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : X.p.Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)),
    (fiberHomFunctor f x y).app j φ =
      (fiberFunctor_restrictObj f x (stageHom j.2)).inv ≫
        (fiberFunctor f (D.obj j.1)).map φ ≫
        (fiberFunctor_restrictObj f y (stageHom j.2)).hom)

#check (AlgebraicGeometry.Groupoids.Hom.fiberHomToLimit :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I}
    (x y : X.p.Fiber (D.obj i)),
    (homCocone c x y).pt ⟶
      (homCocone c ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y)).pt)

#check (AlgebraicGeometry.Groupoids.Hom.fiberHomToLimit_apply :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    (φ : restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)),
    fiberHomToLimit f c x y φ =
      (fiberFunctor_restrictObj f x (c.π.app i)).inv ≫
        (fiberFunctor f c.pt).map φ ≫
        (fiberFunctor_restrictObj f y (c.π.app i)).hom)

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    LimitPreserving (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left),
    (∀ (i : I) (prob : Problem f D c i), ∃ cand : Candidate prob, IsSolution cand) ∧
      ∀ (i : I) (x y : X.p.Fiber (D.obj i))
        [HasColimit (homFunctor x y)]
        [HasColimit (homFunctor ((fiberFunctor f (D.obj i)).obj x)
            ((fiberFunctor f (D.obj i)).obj y))],
        IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
          (colimMap (fiberHomFunctor f x y)) (fiberHomToLimit f c x y)
          (colimit.desc
            (homFunctor ((fiberFunctor f (D.obj i)).obj x)
              ((fiberFunctor f (D.obj i)).obj y))
            (homCocone c ((fiberFunctor f (D.obj i)).obj x)
              ((fiberFunctor f (D.obj i)).obj y))))

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    LimitPreserving f ↔
      (∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
        ∀ (i : I) (prob : Problem f D c i),
          ∃ cand : Candidate prob, IsSolution cand) ∧
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
        ∀ (i : I) (x y : X.p.Fiber (D.obj i))
          [HasColimit (homFunctor x y)]
          [HasColimit (homFunctor ((fiberFunctor f (D.obj i)).obj x)
              ((fiberFunctor f (D.obj i)).obj y))],
          IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
            (colimMap (fiberHomFunctor f x y)) (fiberHomToLimit f c x y)
            (colimit.desc
              (homFunctor ((fiberFunctor f (D.obj i)).obj x)
                ((fiberFunctor f (D.obj i)).obj y))
              (homCocone c ((fiberFunctor f (D.obj i)).obj x)
                ((fiberFunctor f (D.obj i)).obj y))))

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.exists_solution_apply :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (prob : Problem f D c i),
    ∃ cand : Candidate prob, IsSolution cand)

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving.hom_isPullback_apply :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (x y : X.p.Fiber (D.obj i))
    [HasColimit (homFunctor x y)]
    [HasColimit (homFunctor ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y))],
    IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
      (colimMap (fiberHomFunctor f x y)) (fiberHomToLimit f c x y)
      (colimit.desc
        (homFunctor ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y))
        (homCocone c ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y))))
