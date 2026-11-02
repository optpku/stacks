/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Pullback of quasi-coherent modules on groupoid schemes

This module constructs pullback of equivariant quasi-coherent modules along a morphism of
groupoid schemes and records its object, action, and morphism formulas.
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace QCoh

/-- A groupoid-scheme morphism respects source after passing to underlying schemes. -/
theorem map_s_left {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.s.left ≫ f.obj.left = f.arrow.left ≫ H.s.left := by
  simpa using congrArg CategoryTheory.Over.Hom.left f.map_s

/-- A groupoid-scheme morphism respects target after passing to underlying schemes. -/
theorem map_t_left {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    G.t.left ≫ f.obj.left = f.arrow.left ≫ H.t.left := by
  simpa using congrArg CategoryTheory.Over.Hom.left f.map_t

/-- The canonical pullback comparison associated to the source square of a groupoid-scheme
morphism. -/
noncomputable def sourceSquareIso {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    Scheme.QCoh.pullback f.obj.left ⋙ Scheme.QCoh.pullback G.s.left ≅
      Scheme.QCoh.pullback H.s.left ⋙ Scheme.QCoh.pullback f.arrow.left :=
  (pullbackCompIso G.s.left f.obj.left).symm ≪≫
    pullbackEqIso (map_s_left f) ≪≫ pullbackCompIso f.arrow.left H.s.left

/-- The canonical pullback comparison associated to the target square of a groupoid-scheme
morphism. -/
noncomputable def targetSquareIso {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    Scheme.QCoh.pullback f.obj.left ⋙ Scheme.QCoh.pullback G.t.left ≅
      Scheme.QCoh.pullback H.t.left ⋙ Scheme.QCoh.pullback f.arrow.left :=
  (pullbackCompIso G.t.left f.obj.left).symm ≪≫
    pullbackEqIso (map_t_left f) ≪≫ pullbackCompIso f.arrow.left H.t.left

/-- The pullback of the equivariance map along a morphism of groupoid schemes. -/
noncomputable def pullbackAction {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (A : H.QCoh) :
    (Scheme.QCoh.pullback G.t.left).obj ((Scheme.QCoh.pullback f.obj.left).obj A.obj) ⟶
      (Scheme.QCoh.pullback G.s.left).obj ((Scheme.QCoh.pullback f.obj.left).obj A.obj) :=
  (targetSquareIso f).hom.app A.obj ≫
    (Scheme.QCoh.pullback f.arrow.left).map A.action ≫
      (sourceSquareIso f).inv.app A.obj

/-- The pulled-back equivariance map satisfies the cocycle law. -/
theorem pullbackAction_cocycle {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (A : H.QCoh) :
    Cocycle G ((Scheme.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A) := sorry

/-- The pulled-back equivariance map satisfies the unit law. -/
theorem pullbackAction_unit {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (A : H.QCoh) :
    Unit G ((Scheme.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A) := sorry

/-- Pullback of an equivariant quasi-coherent module along a morphism of groupoid schemes. -/
noncomputable def pullbackObj {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (A : H.QCoh) : G.QCoh :=
  of ((Scheme.QCoh.pullback f.obj.left).obj A.obj) (pullbackAction f A)
    (pullbackAction_cocycle f A) (pullbackAction_unit f A)

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of an underlying equivariant morphism remains compatible with equivariance. -/
theorem pullbackMap_compatibility {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) {A B : H.QCoh} (a : A ⟶ B) :
    (Scheme.QCoh.pullback G.t.left).map
          ((Scheme.QCoh.pullback f.obj.left).map (hom a)) ≫ (pullbackObj f B).action =
      (pullbackObj f A).action ≫ (Scheme.QCoh.pullback G.s.left).map
        ((Scheme.QCoh.pullback f.obj.left).map (hom a)) := by
  have ht := (targetSquareIso f).hom.naturality (hom a)
  have hs := (sourceSquareIso f).inv.naturality (hom a)
  dsimp only [Functor.comp_map] at ht hs
  have ha : (Scheme.QCoh.pullback H.t.left).map (hom a) ≫ B.action =
      A.action ≫ (Scheme.QCoh.pullback H.s.left).map (hom a) :=
    (a : System.Hom A B).compatibility
  change (Scheme.QCoh.pullback G.t.left).map
        ((Scheme.QCoh.pullback f.obj.left).map (hom a)) ≫ pullbackAction f B =
      pullbackAction f A ≫ (Scheme.QCoh.pullback G.s.left).map
        ((Scheme.QCoh.pullback f.obj.left).map (hom a))
  dsimp only [pullbackAction]
  calc
    _ = (targetSquareIso f).hom.app A.obj ≫
        (Scheme.QCoh.pullback f.arrow.left).map
          ((Scheme.QCoh.pullback H.t.left).map (hom a) ≫ B.action) ≫
        (sourceSquareIso f).inv.app B.obj := by
      simp only [Functor.map_comp, ← Category.assoc]
      rw [ht]
    _ = (targetSquareIso f).hom.app A.obj ≫
        (Scheme.QCoh.pullback f.arrow.left).map
          (A.action ≫ (Scheme.QCoh.pullback H.s.left).map (hom a)) ≫
        (sourceSquareIso f).inv.app B.obj := by
      rw [ha]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hs]

/-- Pullback of a morphism of equivariant quasi-coherent modules. -/
noncomputable def pullbackMap {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) {A B : H.QCoh} (a : A ⟶ B) : pullbackObj f A ⟶ pullbackObj f B :=
  System.Hom.of ((Scheme.QCoh.pullback f.obj.left).map (hom a))
    (pullbackMap_compatibility f a)

/-- Pullback preserves identity equivariant morphisms. -/
theorem pullbackMap_id {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (A : H.QCoh) :
    pullbackMap f (𝟙 A) = 𝟙 (pullbackObj f A) := by
  change System.Hom.mk _ _ = System.Hom.mk _ _
  congr 1
  exact (Scheme.QCoh.pullback f.obj.left).map_id A.obj

/-- Pullback preserves composition of equivariant morphisms. -/
theorem pullbackMap_comp {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) {A B C : H.QCoh} (a : A ⟶ B) (b : B ⟶ C) :
    pullbackMap f (a ≫ b) = pullbackMap f a ≫ pullbackMap f b := by
  change System.Hom.mk _ _ = System.Hom.mk _ _
  congr 1
  exact (Scheme.QCoh.pullback f.obj.left).map_comp (hom a) (hom b)

/-- Pullback along a morphism of groupoid schemes is a functor on equivariant
quasi-coherent modules. -/
noncomputable def pullback {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    H.QCoh ⥤ G.QCoh where
  obj := pullbackObj f
  map := pullbackMap f
  map_id := pullbackMap_id f
  map_comp := pullbackMap_comp f

/-- The underlying module of a pulled-back equivariant object is ordinary pullback along the
object component. -/
theorem pullback_obj {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    (A : H.QCoh) :
    ((pullback f).obj A).obj = (Scheme.QCoh.pullback f.obj.left).obj A.obj := rfl

/-- The equivariance map of a pulled-back object is the pullback of the original action,
transported across the source and target squares. -/
theorem pullback_action {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    (A : H.QCoh) :
    ((pullback f).obj A).action = pullbackAction f A := rfl

/-- The underlying map of a pulled-back equivariant morphism is ordinary pullback along the
object component. -/
theorem pullback_map {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H)
    {A B : H.QCoh} (a : A ⟶ B) :
    hom ((pullback f).map a) = (Scheme.QCoh.pullback f.obj.left).map (hom a) := rfl

end QCoh

end AlgebraicGeometry.GroupoidScheme
