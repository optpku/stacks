/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Limit-preserving 1-morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is limit
preserving when every directed inverse limit of affine schemes over `S` makes
the square of fibre categories 2-cartesian. This is encoded by essential
surjectivity of the on-objects comparison together with pullback squares of
fibre Hom-colimits.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TypeCat
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

open LimitPreservingOnObjects
open AlgebraicGeometry.Groupoids (homFunctor homCocone)

open CategoryTheory.FiberedCategoryOver.Groupoids.Restriction

-- Rewriting these comparisons requires reducing the fibre and bicategory wrappers.
set_option backward.isDefEq.respectTransparency false

/-- The natural map of directed fibre Hom-diagrams induced by a 1-morphism,
objectwise by the fibre functor and the cartesian comparison
`fiberFunctor_restrictObj`. -/
def fiberHomFunctor {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : X.p.Fiber (D.obj i)) :
    homFunctor x y ⟶
      homFunctor ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y) where
  app j :=
    TypeCat.ofHom fun φ ↦
      (fiberFunctor_restrictObj f x (stageHom j.2)).inv ≫
        (fiberFunctor f (D.obj j.1)).map φ ≫
        (fiberFunctor_restrictObj f y (stageHom j.2)).hom
  naturality := by
    intro j j' g
    apply ConcreteCategory.hom_ext
    intro φ
    have h : stageHom (D := D) (show j.1 ≤ j'.1 from leOfHom g) ≫
        stageHom (D := D) j.2 = stageHom (D := D) j'.2 :=
      (D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr (show j.1 ≤ j'.1 from leOfHom g)))
        (homOfLE (OrderDual.toDual_le_toDual.mpr j.2))).symm.trans
        (congrArg D.map (Subsingleton.elim _ _))
    exact hom_transport_base_comp f x y (stageHom j.2)
      (stageHom (D := D) (show j.1 ≤ j'.1 from leOfHom g)) h φ

/-- The component of `fiberHomFunctor` at a later stage is the fibre functor on
Hom-types, transported along `fiberFunctor_restrictObj`. -/
theorem fiberHomFunctor_app {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : X.p.Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    (fiberHomFunctor f x y).app j φ =
      (fiberFunctor_restrictObj f x (stageHom j.2)).inv ≫
        (fiberFunctor f (D.obj j.1)).map φ ≫
        (fiberFunctor_restrictObj f y (stageHom j.2)).hom := rfl

/-- The comparison of fibre Hom-types over the cone point induced by a
1-morphism, via the fibre functor over the limit and
`fiberFunctor_restrictObj` along the cone projection. -/
def fiberHomToLimit {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I}
    (x y : X.p.Fiber (D.obj i)) :
    (homCocone c x y).pt ⟶
      (homCocone c ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y)).pt :=
  TypeCat.ofHom fun φ ↦
    (fiberFunctor_restrictObj f x (c.π.app i)).inv ≫
      (fiberFunctor f c.pt).map φ ≫
      (fiberFunctor_restrictObj f y (c.π.app i)).hom

/-- `fiberHomToLimit` applies the fibre functor over the cone point and
transports along `fiberFunctor_restrictObj`. -/
theorem fiberHomToLimit_apply {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    (φ : restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)) :
    fiberHomToLimit f c x y φ =
      (fiberFunctor_restrictObj f x (c.π.app i)).inv ≫
        (fiberFunctor f c.pt).map φ ≫
        (fiberFunctor_restrictObj f y (c.π.app i)).hom := rfl

/-- The stage comparison and the cone-point comparison commute with each cocone leg. -/
theorem fiberHomToLimit_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i)) (j : Set.Ici i) :
    (homCocone c x y).ι.app j ≫ fiberHomToLimit f c x y =
      (fiberHomFunctor f x y).app j ≫
        (homCocone c ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y)).ι.app j := by
  apply ConcreteCategory.hom_ext
  intro φ
  exact hom_transport_base_comp f x y (stageHom j.2) (c.π.app j.1)
    (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr j.2))) φ

/-- The actual colimit comparison square is induced by the commuting stage squares. -/
theorem fiberHom_colimit_w {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    [HasColimit (homFunctor x y)]
    [HasColimit (homFunctor ((fiberFunctor f (D.obj i)).obj x)
      ((fiberFunctor f (D.obj i)).obj y))] :
    colimit.desc (homFunctor x y) (homCocone c x y) ≫ fiberHomToLimit f c x y =
      colimMap (fiberHomFunctor f x y) ≫
        colimit.desc (homFunctor ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y))
          (homCocone c ((fiberFunctor f (D.obj i)).obj x)
            ((fiberFunctor f (D.obj i)).obj y)) := by
  apply colimit.hom_ext
  intro j
  simpa using fiberHomToLimit_naturality f c x y j

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is limit
preserving when every directed affine inverse limit yields a 2-cartesian square
of fibre categories. -/
class LimitPreserving {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Prop where
  /-- Every directed affine inverse-limit problem admits a commuting on-objects
  solution. -/
  exists_solution : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ (i : I) (prob : Problem f D c i), ∃ cand : Candidate prob, IsSolution cand
  /-- Fibre Hom-colimit squares along directed affine inverse limits are
  pullbacks. -/
  hom_isPullback : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
            ((fiberFunctor f (D.obj i)).obj y)))

namespace LimitPreserving

/-- The identity 1-morphism is limit preserving. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    LimitPreserving (𝟙 X) where
  exists_solution := LimitPreservingOnObjects.id.exists_solution
  hom_isPullback := by
    intro I _ _ _ D c hc hD hpt i x y _ _
    have hf : fiberHomFunctor (𝟙 X) x y = 𝟙 (Groupoids.homFunctor x y) := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro φ
      change (fiberFunctor_restrictObj (𝟙 X) x (stageHom j.2)).inv ≫ φ ≫
        (fiberFunctor_restrictObj (𝟙 X) y (stageHom j.2)).hom = φ
      rw [comparison_id, comparison_id]
      exact (Category.id_comp (φ ≫ 𝟙 _)).trans (Category.comp_id φ)
    have hl : fiberHomToLimit (𝟙 X) c x y = 𝟙 (Groupoids.homCocone c x y).pt := by
      apply ConcreteCategory.hom_ext
      intro φ
      change (fiberFunctor_restrictObj (𝟙 X) x (c.π.app i)).inv ≫ φ ≫
        (fiberFunctor_restrictObj (𝟙 X) y (c.π.app i)).hom = φ
      rw [comparison_id, comparison_id]
      exact (Category.id_comp (φ ≫ 𝟙 _)).trans (Category.comp_id φ)
    have hm : colimMap (𝟙 (Groupoids.homFunctor x y)) = 𝟙 _ := by
      apply colimit.hom_ext
      intro j
      simp
    rw [hf, hm, hl]
    exact IsPullback.of_vert_isIso
      ⟨(Category.comp_id _).trans (Category.id_comp _).symm⟩

/-- The composition of two limit-preserving 1-morphisms of categories fibred in
groupoids over `(Sch/S)_fppf` is limit preserving. -/
@[stacks 0CMU]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [LimitPreserving p] [LimitPreserving q] :
    LimitPreserving (p ≫ q) where
  exists_solution := by
    letI : LimitPreservingOnObjects p := ⟨LimitPreserving.exists_solution (f := p)⟩
    letI : LimitPreservingOnObjects q := ⟨LimitPreserving.exists_solution (f := q)⟩
    intro I _ _ _ D c hc hD hpt i prob
    exact (LimitPreservingOnObjects.comp p q).exists_solution D c hc hD hpt i prob
  hom_isPullback := by
    intro I _ _ _ D c hc hD hpt i x y _ _
    have hf : fiberHomFunctor (p ≫ q) x y =
        fiberHomFunctor p x y ≫
          fiberHomFunctor q ((fiberFunctor p (D.obj i)).obj x)
            ((fiberFunctor p (D.obj i)).obj y) := by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro φ
      exact hom_transport_comp p q x y (stageHom j.2) φ
    have hl : fiberHomToLimit (p ≫ q) c x y =
        fiberHomToLimit p c x y ≫
          fiberHomToLimit q c ((fiberFunctor p (D.obj i)).obj x)
            ((fiberFunctor p (D.obj i)).obj y) := by
      apply ConcreteCategory.hom_ext
      intro φ
      exact hom_transport_comp p q x y (c.π.app i) φ
    have hm : colimMap (fiberHomFunctor (p ≫ q) x y) =
        colimMap (fiberHomFunctor p x y) ≫
          colimMap (fiberHomFunctor q ((fiberFunctor p (D.obj i)).obj x)
            ((fiberFunctor p (D.obj i)).obj y)) := by
      rw [hf]
      apply colimit.hom_ext
      intro j
      simp
      rfl
    rw [hm, hl]
    exact (LimitPreserving.hom_isPullback (f := p) D c hc hD hpt i x y).paste_vert
      (LimitPreserving.hom_isPullback (f := q) D c hc hD hpt i
        ((fiberFunctor p (D.obj i)).obj x) ((fiberFunctor p (D.obj i)).obj y))

/-- Limit preservation of a 1-morphism means on-objects solvability together with
pullbacks of fibre Hom-colimits, both taken over directed affine inverse
systems. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) :
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
              ((fiberFunctor f (D.obj i)).obj y))) :=
  ⟨exists_solution D c hc hD hpt, hom_isPullback D c hc hD hpt⟩

/-- Being a limit-preserving 1-morphism is equivalent to on-objects solvability
and Hom-colimit pullbacks on every directed affine inverse system over `S`. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
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
                ((fiberFunctor f (D.obj i)).obj y))) := by
  constructor
  · intro h
    exact ⟨h.exists_solution, h.hom_isPullback⟩
  · rintro ⟨hobj, hhom⟩
    exact ⟨hobj, hhom⟩

/-- A limit-preserving 1-morphism admits a solution for every directed affine
inverse-limit problem. -/
theorem exists_solution_apply {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (prob : Problem f D c i) :
    ∃ cand : Candidate prob, IsSolution cand :=
  exists_solution D c hc hD hpt i prob

/-- A limit-preserving 1-morphism yields a pullback of fibre Hom-colimits along
every directed affine inverse limit. -/
theorem hom_isPullback_apply {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (x y : X.p.Fiber (D.obj i))
    [HasColimit (homFunctor x y)]
    [HasColimit (homFunctor ((fiberFunctor f (D.obj i)).obj x)
        ((fiberFunctor f (D.obj i)).obj y))] :
    IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
      (colimMap (fiberHomFunctor f x y)) (fiberHomToLimit f c x y)
      (colimit.desc
        (homFunctor ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y))
        (homCocone c ((fiberFunctor f (D.obj i)).obj x)
          ((fiberFunctor f (D.obj i)).obj y))) :=
  hom_isPullback D c hc hD hpt i x y

/-- A limit-preserving 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` is limit preserving on objects. -/
@[stacks 0CMS]
instance toLimitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] :
    LimitPreservingOnObjects f where
  exists_solution := exists_solution (f := f)

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
