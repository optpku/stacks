module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap97.«97_5_0_1_Restrict»
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving

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
  naturality := sorry

/-- The component of `fiberHomFunctor` at a later stage is the fibre functor on
Hom-types, transported along `fiberFunctor_restrictObj`. -/
theorem fiberHomFunctor_app {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : X.p.Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    (fiberHomFunctor f x y).app j φ =
      (fiberFunctor_restrictObj f x (stageHom j.2)).inv ≫
        (fiberFunctor f (D.obj j.1)).map φ ≫
        (fiberFunctor_restrictObj f y (stageHom j.2)).hom := sorry

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
        (fiberFunctor_restrictObj f y (c.π.app i)).hom := sorry

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
    LimitPreserving (𝟙 X) := sorry

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
              ((fiberFunctor f (D.obj i)).obj y))) := sorry

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
                ((fiberFunctor f (D.obj i)).obj y))) := sorry

/-- A limit-preserving 1-morphism admits a solution for every directed affine
inverse-limit problem. -/
theorem exists_solution_apply {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LimitPreserving f] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (prob : Problem f D c i) :
    ∃ cand : Candidate prob, IsSolution cand := sorry

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
          ((fiberFunctor f (D.obj i)).obj y))) := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids.Hom
