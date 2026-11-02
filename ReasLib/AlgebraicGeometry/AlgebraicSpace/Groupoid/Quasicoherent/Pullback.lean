/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-!
# Pullback of quasi-coherent modules on groupoids in algebraic spaces

This module constructs pullback of equivariant quasi-coherent modules along a morphism of
groupoids in algebraic spaces and records its object, action, and morphism formulas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace QCoh

/-- A groupoid morphism respects source after passing to underlying algebraic spaces. -/
def map_s_left {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.s.left ≫ f.obj.left = f.arrow.left ≫ H.s.left :=
  (Over.comp_left G.R G.U H.U G.s f.obj).symm.trans
    ((congrArg (fun k : G.R ⟶ H.U ↦ k.left) f.map_s).trans (Over.comp_left G.R H.R H.U f.arrow H.s))

/-- A groupoid morphism respects target after passing to underlying algebraic spaces. -/
def map_t_left {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : G.t.left ≫ f.obj.left = f.arrow.left ≫ H.t.left :=
  (Over.comp_left G.R G.U H.U G.t f.obj).symm.trans
    ((congrArg (fun k : G.R ⟶ H.U ↦ k.left) f.map_t).trans (Over.comp_left G.R H.R H.U f.arrow H.t))

/-- The canonical pullback comparison associated to the source square of a groupoid morphism. -/
def sourceSquareIso {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) :
    AlgebraicSpace.QCoh.pullback f.obj.left ⋙ AlgebraicSpace.QCoh.pullback G.s.left ≅
      AlgebraicSpace.QCoh.pullback H.s.left ⋙ AlgebraicSpace.QCoh.pullback f.arrow.left :=
  (AlgebraicSpace.QCoh.pullbackCompIso f.obj.left G.s.left) ≪≫
    pullbackEqIso (map_s_left f) ≪≫ (AlgebraicSpace.QCoh.pullbackCompIso H.s.left f.arrow.left).symm

/-- The canonical pullback comparison associated to the target square of a groupoid morphism. -/
def targetSquareIso {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) :
    AlgebraicSpace.QCoh.pullback f.obj.left ⋙ AlgebraicSpace.QCoh.pullback G.t.left ≅
      AlgebraicSpace.QCoh.pullback H.t.left ⋙ AlgebraicSpace.QCoh.pullback f.arrow.left :=
  (AlgebraicSpace.QCoh.pullbackCompIso f.obj.left G.t.left) ≪≫
    pullbackEqIso (map_t_left f) ≪≫ (AlgebraicSpace.QCoh.pullbackCompIso H.t.left f.arrow.left).symm

/-- The pullback of the equivariance map along a morphism of groupoids in algebraic spaces. -/
def pullbackAction {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) (A : H.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj
        ((AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj) ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj
        ((AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj) :=
  (targetSquareIso f).hom.app A.obj ≫
    (AlgebraicSpace.QCoh.pullback f.arrow.left).map A.action ≫
      (sourceSquareIso f).inv.app A.obj

/-- The pulled-back equivariance map satisfies the cocycle law. -/
theorem pullbackAction_cocycle {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (A : H.QCoh) :
    Cocycle G ((AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A) :=
  sorry

/-- The pulled-back equivariance map satisfies the unit law. -/
theorem pullbackAction_unit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (A : H.QCoh) :
    Unit G ((AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A) :=
  sorry

/-- Pullback of an equivariant quasi-coherent module along a morphism of groupoids. -/
def pullbackObj {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) (A : H.QCoh) : G.QCoh :=
  of ((AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A)
    (pullbackAction_cocycle f A) (pullbackAction_unit f A)

private theorem mapAction_compatibility
    {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    (F : C ⥤ D) (R : E ⥤ K) (t s : C ⥤ E) (t' s' : D ⥤ K)
    (α : F ⋙ t' ⟶ t ⋙ R) (β : s ⋙ R ⟶ F ⋙ s')
    {M N : C} (a : M ⟶ N) (m : t.obj M ⟶ s.obj M) (n : t.obj N ⟶ s.obj N)
    (h : t.map a ≫ n = m ≫ s.map a) :
    t'.map (F.map a) ≫ (α.app N ≫ R.map n ≫ β.app N) =
      (α.app M ≫ R.map m ≫ β.app M) ≫ s'.map (F.map a) := by
  have ht := α.naturality a
  have hs := β.naturality a
  dsimp only [Functor.comp_map] at ht hs
  have ha := congrArg R.map h
  simp only [Functor.map_comp] at ha
  erw [← Category.assoc, ht, Category.assoc (α.app M),
    ← Category.assoc (R.map (t.map a)) (R.map n), ha,
    Category.assoc (R.map m), hs,
    ← Category.assoc (R.map m) (β.app M), ← Category.assoc]
  rfl

/-- Pullback of an underlying equivariant morphism remains compatible with equivariance. -/
theorem pullbackMap_compatibility {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {M N : H.QCoh} (a : M ⟶ N) :
    (AlgebraicSpace.QCoh.pullback G.t.left).map
          ((AlgebraicSpace.QCoh.pullback f.obj.left).map (hom a)) ≫
        (pullbackObj f N).action =
      (pullbackObj f M).action ≫
        (AlgebraicSpace.QCoh.pullback G.s.left).map
          ((AlgebraicSpace.QCoh.pullback f.obj.left).map (hom a)) := by
  exact mapAction_compatibility
    (AlgebraicSpace.QCoh.pullback f.obj.left) (AlgebraicSpace.QCoh.pullback f.arrow.left)
    (AlgebraicSpace.QCoh.pullback H.t.left) (AlgebraicSpace.QCoh.pullback H.s.left)
    (AlgebraicSpace.QCoh.pullback G.t.left) (AlgebraicSpace.QCoh.pullback G.s.left)
    (targetSquareIso f).hom (sourceSquareIso f).inv (hom a) M.action N.action a.compatibility

/-- Pullback of a morphism of equivariant quasi-coherent modules. -/
def pullbackMap {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {M N : H.QCoh} (a : M ⟶ N) : pullbackObj f M ⟶ pullbackObj f N :=
  System.Hom.of ((AlgebraicSpace.QCoh.pullback f.obj.left).map (hom a))
    (pullbackMap_compatibility f a)

/-- Pullback preserves identity equivariant morphisms. -/
theorem pullbackMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (A : H.QCoh) :
    pullbackMap f (𝟙 A) = 𝟙 (pullbackObj f A) := by
  change System.Hom.mk _ _ = System.Hom.mk _ _
  congr 1
  exact (AlgebraicSpace.QCoh.pullback f.obj.left).map_id A.obj

/-- Pullback preserves composition of equivariant morphisms. -/
theorem pullbackMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) {M N P : H.QCoh} (a : M ⟶ N) (b : N ⟶ P) :
    pullbackMap f (a ≫ b) = pullbackMap f a ≫ pullbackMap f b := by
  change System.Hom.mk _ _ = System.Hom.mk _ _
  congr 1
  exact (AlgebraicSpace.QCoh.pullback f.obj.left).map_comp (hom a) (hom b)

/-- Pullback along a morphism of groupoids in algebraic spaces is a functor on equivariant
quasi-coherent modules. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) : H.QCoh ⥤ G.QCoh where
  obj := pullbackObj f
  map := pullbackMap f
  map_id := pullbackMap_id f
  map_comp := pullbackMap_comp f

/-- The underlying module of a pulled-back equivariant object is ordinary pullback along the
object component. -/
theorem pullback_obj {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) (A : H.QCoh) :
    ((pullback f).obj A).obj = (AlgebraicSpace.QCoh.pullback f.obj.left).obj A.obj := rfl

/-- The equivariance map of a pulled-back object is the pullback of the original action,
transported across the source and target squares. -/
theorem pullback_action {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (A : H.QCoh) :
    ((pullback f).obj A).action = pullbackAction f A := rfl

/-- The underlying map of a pulled-back equivariant morphism is ordinary pullback along the
object component. -/
theorem pullback_map {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) {M N : H.QCoh} (a : M ⟶ N) :
    hom ((pullback f).map a) = (AlgebraicSpace.QCoh.pullback f.obj.left).map (hom a) := rfl

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace
