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

-- Rewriting these comparisons requires reducing the fibre and bicategory wrappers.
set_option backward.isDefEq.respectTransparency false

@[reassoc] private theorem comparison_hom_fac {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U V : Over S} (x : X.p.Fiber U) (g : V ⟶ U) :
    (fiberFunctor_restrictObj f x g).hom.1 ≫
        IsPreFibered.pullbackMap ((fiberFunctor f U).obj x).property g =
      (toFunctor f).map (IsPreFibered.pullbackMap x.property g) := by
  exact @IsCartesian.fac _ _ _ _ Y.p _ _ _ _ g
    (IsPreFibered.pullbackMap ((fiberFunctor f U).obj x).property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _
    ((toFunctor f).map (IsPreFibered.pullbackMap x.property g))
    (map_restrict_isCartesian f x g).toIsHomLift

@[reassoc] private theorem restriction_hom_fac {S : Scheme.{u}} {X : GroupoidsOver S}
    {U V : Over S} {x y : X.p.Fiber U} (φ : x ⟶ y) (g : V ⟶ U) :
    (restrictHom φ g).1 ≫ IsPreFibered.pullbackMap y.property g =
      IsPreFibered.pullbackMap x.property g ≫ φ.1 := by
  exact @IsCartesian.fac _ _ _ _ X.p _ _ _ _ g
    (IsPreFibered.pullbackMap y.property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _
    (IsPreFibered.pullbackMap x.property g ≫ φ.1)
    (@IsHomLift.comp_lift_id_right _ _ _ _ X.p _ _ _ _ _ g
      (IsPreFibered.pullbackMap x.property g)
      (IsPreFibered.pullbackMap.IsCartesian _ _).toIsHomLift φ.1 φ.2)

@[reassoc] private theorem restriction_comp_hom_fac {S : Scheme.{u}} {X : GroupoidsOver S}
    {U V W : Over S} (x : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V) :
    (restrictObj_comp x a b).hom.1 ≫
        IsPreFibered.pullbackMap x.property (b ≫ a) =
      IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a := by
  letI : X.p.IsCartesian (b ≫ a)
      (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a) :=
    @IsFibered.comp _ _ _ _ X.p inferInstance _ _ _ b a _ _ _
      (IsPreFibered.pullbackMap (restrictObj x a).property b)
      (IsPreFibered.pullbackMap x.property a)
      (IsPreFibered.pullbackMap.IsCartesian _ _)
      (IsPreFibered.pullbackMap.IsCartesian _ _)
  change IsCartesian.map X.p (b ≫ a)
    (IsPreFibered.pullbackMap x.property (b ≫ a))
    (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
      IsPreFibered.pullbackMap x.property a) ≫ _ = _
  exact
    (@IsCartesian.fac _ _ _ _ X.p _ _ _ _ (b ≫ a)
      (IsPreFibered.pullbackMap x.property (b ≫ a))
      (IsPreFibered.pullbackMap.IsCartesian _ _) _
      (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a) inferInstance)

private theorem restriction_ext {S : Scheme.{u}} {X : GroupoidsOver S}
    {U V : Over S} (y : X.p.Fiber U) (g : V ⟶ U) {z : X.p.Fiber V}
    {φ ψ : z ⟶ restrictObj y g}
    (h : φ.1 ≫ IsPreFibered.pullbackMap y.property g =
      ψ.1 ≫ IsPreFibered.pullbackMap y.property g) : φ = ψ := by
  apply Subtype.ext
  exact @IsCartesian.ext _ _ _ _ X.p _ _ _ _ g
    (IsPreFibered.pullbackMap y.property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ φ.1 ψ.1 φ.2 ψ.2 h

private theorem comparison_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) {U V : Over S} (x : X.p.Fiber U) (g : V ⟶ U) :
    fiberFunctor_restrictObj (p ≫ q) x g =
      (fiberFunctor q V).mapIso (fiberFunctor_restrictObj p x g) ≪≫
        fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g := by
  apply Iso.ext
  apply restriction_ext
  change (fiberFunctor_restrictObj (p ≫ q) x g).hom.1 ≫ _ =
    ((toFunctor q).map (fiberFunctor_restrictObj p x g).hom.1 ≫
      (fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g).hom.1) ≫ _
  rw [Category.assoc, comparison_hom_fac, comparison_hom_fac,
    ← Functor.map_comp, comparison_hom_fac]
  rfl

private theorem comparison_id {S : Scheme.{u}} {X : GroupoidsOver S}
    {U V : Over S} (x : X.p.Fiber U) (g : V ⟶ U) :
    fiberFunctor_restrictObj (𝟙 X) x g = Iso.refl (restrictObj x g) := by
  apply Iso.ext
  apply restriction_ext
  rw [comparison_hom_fac]
  exact (Category.id_comp _).symm

private theorem restriction_comp {S : Scheme.{u}} {X : GroupoidsOver S}
    {U V : Over S} {x y z : X.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) (g : V ⟶ U) :
    restrictHom (φ ≫ ψ) g = restrictHom φ g ≫ restrictHom ψ g := by
  apply restriction_ext
  change (restrictHom (φ ≫ ψ) g).1 ≫ _ =
    ((restrictHom φ g).1 ≫ (restrictHom ψ g).1) ≫ _
  simp only [Category.assoc, restriction_hom_fac, restriction_hom_fac_assoc]
  rfl

@[reassoc] private theorem comparison_restriction {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U V : Over S} {x y : X.p.Fiber U} (φ : x ⟶ y) (g : V ⟶ U) :
    (fiberFunctor_restrictObj f x g).inv ≫
        (fiberFunctor f V).map (restrictHom φ g) ≫
        (fiberFunctor_restrictObj f y g).hom =
      restrictHom ((fiberFunctor f U).map φ) g := by
  apply (Iso.inv_comp_eq _).mpr
  apply restriction_ext
  change ((toFunctor f).map (restrictHom φ g).1 ≫
    (fiberFunctor_restrictObj f y g).hom.1) ≫ _ =
    ((fiberFunctor_restrictObj f x g).hom.1 ≫
      (restrictHom ((fiberFunctor f U).map φ) g).1) ≫ _
  simp only [Category.assoc, comparison_hom_fac, comparison_hom_fac_assoc,
    restriction_hom_fac]
  change (toFunctor f).map (restrictHom φ g).1 ≫
      (toFunctor f).map (IsPreFibered.pullbackMap y.property g) =
    (toFunctor f).map (IsPreFibered.pullbackMap x.property g) ≫ (toFunctor f).map φ.1
  simpa only [Functor.map_comp] using
    congrArg (toFunctor f).map (restriction_hom_fac φ g)

private theorem comparison_base_comp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U V W : Over S} (x : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V) :
    (fiberFunctor f W).mapIso (restrictObj_comp x a b) ≪≫
        fiberFunctor_restrictObj f x (b ≫ a) =
      fiberFunctor_restrictObj f (restrictObj x a) b ≪≫
        restrictIso (fiberFunctor_restrictObj f x a) b ≪≫
        restrictObj_comp ((fiberFunctor f U).obj x) a b := by
  apply Iso.ext
  apply restriction_ext
  change ((toFunctor f).map (restrictObj_comp x a b).hom.1 ≫
      (fiberFunctor_restrictObj f x (b ≫ a)).hom.1) ≫ _ =
    ((fiberFunctor_restrictObj f (restrictObj x a) b).hom.1 ≫
      (restrictHom (fiberFunctor_restrictObj f x a).hom b).1 ≫
      (restrictObj_comp ((fiberFunctor f U).obj x) a b).hom.1) ≫ _
  have hx := restriction_comp_hom_fac x a b
  have hy := restriction_comp_hom_fac ((fiberFunctor f U).obj x) a b
  simp only [Category.assoc, comparison_hom_fac, comparison_hom_fac_assoc,
    hy, restriction_hom_fac_assoc, ← Functor.map_comp, hx]

private theorem hom_transport_base_comp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U V W : Over S} (x y : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V)
    {d : W ⟶ U} (h : b ≫ a = d) (φ : restrictObj x a ⟶ restrictObj y a) :
    (fiberFunctor_restrictObj f x d).inv ≫
        (fiberFunctor f W).map
          ((restrictObj_comp x a b ≪≫ restrictObj_eq x h).inv ≫
            restrictHom φ b ≫ (restrictObj_comp y a b ≪≫ restrictObj_eq y h).hom) ≫
        (fiberFunctor_restrictObj f y d).hom =
      (restrictObj_comp ((fiberFunctor f U).obj x) a b ≪≫
          restrictObj_eq ((fiberFunctor f U).obj x) h).inv ≫
        restrictHom ((fiberFunctor_restrictObj f x a).inv ≫
          (fiberFunctor f V).map φ ≫ (fiberFunctor_restrictObj f y a).hom) b ≫
        (restrictObj_comp ((fiberFunctor f U).obj y) a b ≪≫
          restrictObj_eq ((fiberFunctor f U).obj y) h).hom := by
  subst d
  simp only [restrictObj_eq, eqToIso_refl, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp]
  have he (z : X.p.Fiber U) :
      fiberFunctor_restrictObj f z (b ≫ a) =
        ((fiberFunctor f W).mapIso (restrictObj_comp z a b)).symm ≪≫
          fiberFunctor_restrictObj f (restrictObj z a) b ≪≫
            restrictIso (fiberFunctor_restrictObj f z a) b ≪≫
              restrictObj_comp ((fiberFunctor f U).obj z) a b := by
    apply Iso.ext
    apply (Iso.eq_inv_comp _).mpr
    exact congrArg Iso.hom (comparison_base_comp f z a b)
  rw [he x, he y]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, restriction_comp,
    Category.assoc, Iso.map_hom_inv_id_assoc,
    comparison_restriction_assoc]
  rfl

private theorem hom_transport_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) {U V : Over S} (x y : X.p.Fiber U) (g : V ⟶ U)
    (φ : restrictObj x g ⟶ restrictObj y g) :
    (fiberFunctor_restrictObj (p ≫ q) x g).inv ≫
        (fiberFunctor (p ≫ q) V).map φ ≫
        (fiberFunctor_restrictObj (p ≫ q) y g).hom =
      (fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g).inv ≫
        (fiberFunctor q V).map ((fiberFunctor_restrictObj p x g).inv ≫
          (fiberFunctor p V).map φ ≫ (fiberFunctor_restrictObj p y g).hom) ≫
        (fiberFunctor_restrictObj q ((fiberFunctor p U).obj y) g).hom := by
  rw [comparison_comp, comparison_comp]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rfl

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
