/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Relative morphisms of algebraic spaces

A test morphism `a : ofOver T ⟶ B` determines fibre products `pullback a z` and
`pullback a x`. A relative morphism over `ofOver T` is an arrow between those
objects in `Over (ofOver T)`. Pairs `(a, b)` package the test morphism with that
arrow.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Morphisms over `ofOver T` between the fibre products `pullback a z` and
`pullback a x`. -/
abbrev BaseChangeMorphism {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) {T : Over S} (a : ofOver T ⟶ B) : Type (u + 1) :=
  Over.mk (pullback.fst a z) ⟶ Over.mk (pullback.fst a x)

/-- A pair `(a, b)` consisting of a test morphism `a : ofOver T ⟶ B` and a
morphism `b` over `ofOver T` from `pullback a z` to `pullback a x`. -/
structure Pair {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) (T : Over S) : Type (u + 1) where
  /-- The test morphism `a : ofOver T ⟶ B`. -/
  a : ofOver T ⟶ B
  /-- The morphism over `ofOver T` between the fibre products with `Z` and `X`. -/
  b : BaseChangeMorphism z x a

/-- Construct a pair from a test morphism `a` and a morphism `b` over `ofOver T`. -/
def mk {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B Z X : AlgebraicSpace S}
    {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} (a : ofOver T ⟶ B) (b : BaseChangeMorphism z x a) : Pair z x T where
  a := a
  b := b

namespace BaseChangeMorphism

/-- The underlying arrow of `b` commutes with the projections to `ofOver T`. -/
theorem over_fst {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    b.left ≫ pullback.fst a x = pullback.fst a z :=
  Over.w b

/-- View `b` as a morphism `pullback a z ⟶ X`. -/
def toMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    pullback a z ⟶ X :=
  b.left ≫ pullback.snd a x

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `toMap b` makes the triangle over `B` commute. -/
theorem toMap_comm {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    toMap b ≫ x = pullback.fst a z ≫ a := by
  calc
    toMap b ≫ x = b.left ≫ (pullback.snd a x ≫ x) := Category.assoc _ _ _
    _ = b.left ≫ (pullback.fst a x ≫ a) :=
      congrArg (fun f : pullback a x ⟶ B ↦ b.left ≫ f) pullback.condition.symm
    _ = (b.left ≫ pullback.fst a x) ≫ a := (Category.assoc _ _ _).symm
    _ = pullback.fst a z ≫ a :=
      congrArg (fun f : pullback a z ⟶ ofOver T ↦ f ≫ a) (over_fst b)

/-- The morphism `pullback a z ⟶ pullback a x` induced by a map to `X` making the
triangle over `B` commute. -/
def ofMap_left {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : pullback a z ⟶ pullback a x :=
  pullback.lift (pullback.fst a z) b' h.symm

/-- `ofMap_left b' h` projects to `ofOver T` as `pullback.fst a z`. -/
theorem ofMap_left_fst {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) :
    ofMap_left b' h ≫ pullback.fst a x = pullback.fst a z :=
  pullback.lift_fst _ _ _

/-- Reconstruct a morphism over `ofOver T` from a map `pullback a z ⟶ X` making
the triangle over `B` commute. -/
def ofMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : BaseChangeMorphism z x a :=
  Over.homMk (ofMap_left b' h) (ofMap_left_fst b' h)

/-- `ofMap` recovers `b` from `toMap b`. -/
theorem ofMap_toMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    ofMap (toMap b) (toMap_comm b) = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (over_fst _).trans (over_fst b).symm
  · exact pullback.lift_snd _ _ _

/-- `toMap` recovers the original map into `X` from `ofMap`. -/
theorem toMap_ofMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : toMap (ofMap b' h) = b' :=
  pullback.lift_snd _ _ _

end BaseChangeMorphism

/-- The components of a pair are a test morphism and a morphism over `ofOver T`. -/
theorem Pair.spec {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} (p : Pair z x T) :
    p.b.left ≫ pullback.fst p.a x = pullback.fst p.a z :=
  BaseChangeMorphism.over_fst p.b

variable {S : Scheme.{u}} {Z X B : AlgebraicSpace S}

namespace Pair

/-- Base change of a relative morphism preserves its triangle over the base. -/
theorem restrict_w {g : Z ⟶ B} {h : X ⟶ B} {T T' : Over S}
    (p : Pair g h T) (φ : T' ⟶ T) :
    (pullback.map (C := AlgebraicSpace S) (W := ofOver T') (Y := ofOver T) ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.a) g p.a g
      ((yoneda.map φ : ofOver T' ⟶ ofOver T)) (𝟙 Z) (𝟙 B)
      (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm) ≫
        BaseChangeMorphism.toMap p.b) ≫ h =
      pullback.fst (C := AlgebraicSpace S) (X := ofOver T') ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.a) g ≫ ((yoneda.map φ : ofOver T' ⟶ ofOver T) ≫ p.a) := by
  rw [Category.assoc, BaseChangeMorphism.toMap_comm, ← Category.assoc,
    pullback.lift_fst, Category.assoc]

/-- Restrict a relative morphism by the canonical map between the base changes. -/
def restrict {g : Z ⟶ B} {h : X ⟶ B} {T T' : Over S}
    (p : Pair g h T) (φ : T' ⟶ T) : Pair g h T' :=
  let a' : ofOver T' ⟶ B := yoneda.map φ ≫ p.a
  let c : pullback a' g ⟶ pullback p.a g :=
    pullback.map (C := AlgebraicSpace S) (W := ofOver T') (Y := ofOver T)
      a' g p.a g (yoneda.map φ) (𝟙 Z) (𝟙 B)
      (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm)
  mk a' (BaseChangeMorphism.ofMap (z := g) (x := h) (T := T') (a := a')
    (c ≫ BaseChangeMorphism.toMap p.b)
    (restrict_w (g := g) (h := h) (T := T) (T' := T') p φ))

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a relative morphism along an identity leaves it unchanged. -/
theorem restrict_id {g : Z ⟶ B} {h : X ⟶ B} {T : Over S}
    (p : Pair g h T) : p.restrict (𝟙 T) = p := by
  rcases p with ⟨a, b⟩
  let R (f : ofOver T ⟶ ofOver T) : Pair g h T :=
    mk (f ≫ a) (BaseChangeMorphism.ofMap
      (pullback.map (f ≫ a) g a g f (𝟙 Z) (𝟙 B)
        (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm) ≫
          BaseChangeMorphism.toMap b)
      (by rw [Category.assoc, BaseChangeMorphism.toMap_comm, ← Category.assoc,
        pullback.lift_fst, Category.assoc]))
  have hid : (yoneda.map (𝟙 T) : ofOver T ⟶ ofOver T) = 𝟙 (ofOver T) :=
    yoneda.map_id T
  change R (yoneda.map (𝟙 T)) = Pair.mk a b
  rw [hid]
  dsimp only [R]
  apply congrArg (mk a)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (BaseChangeMorphism.over_fst _).trans
      (BaseChangeMorphism.over_fst b).symm
  · change BaseChangeMorphism.toMap _ = BaseChangeMorphism.toMap b
    simp only [BaseChangeMorphism.toMap_ofMap]
    exact (congrArg (fun f : pullback a g ⟶ pullback a g ↦
      f ≫ BaseChangeMorphism.toMap b) (pullback.map_id (f := a) (g := g))).trans
        (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a composite agrees with successive restriction. -/
theorem restrict_comp {g : Z ⟶ B} {h : X ⟶ B} {T T' T'' : Over S}
    (p : Pair g h T) (φ : T'' ⟶ T') (ψ : T' ⟶ T) :
    p.restrict (φ ≫ ψ) = (p.restrict ψ).restrict φ := by
  let R {U V : Over S} (q : Pair g h V) (f : ofOver U ⟶ ofOver V) : Pair g h U :=
    mk (f ≫ q.a) (BaseChangeMorphism.ofMap
      (pullback.map (f ≫ q.a) g q.a g f (𝟙 Z) (𝟙 B)
        (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm) ≫
          BaseChangeMorphism.toMap q.b)
      (by rw [Category.assoc, BaseChangeMorphism.toMap_comm, ← Category.assoc,
        pullback.lift_fst, Category.assoc]))
  have hcomp : (yoneda.map (φ ≫ ψ) : ofOver T'' ⟶ ofOver T) =
      (yoneda.map φ : ofOver T'' ⟶ ofOver T') ≫
        (yoneda.map ψ : ofOver T' ⟶ ofOver T) := yoneda.map_comp φ ψ
  change R p (yoneda.map (φ ≫ ψ)) = R (R p (yoneda.map ψ)) (yoneda.map φ)
  rw [hcomp]
  dsimp only [R]
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (BaseChangeMorphism.over_fst _).trans
      (BaseChangeMorphism.over_fst _).symm
  · change BaseChangeMorphism.toMap _ = BaseChangeMorphism.toMap _
    simp only [BaseChangeMorphism.toMap_ofMap, ← Category.assoc,
      pullback.map_comp, Category.id_comp]
    rfl

end Pair

/-- The presheaf of relative morphisms from `Z` to `X` over `B`. -/
def presheaf (g : Z ⟶ B) (h : X ⟶ B) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Pair g h T.unop
  map φ := TypeCat.ofHom fun p ↦ p.restrict φ.unop
  map_id := by
    intro T
    ext p
    exact Pair.restrict_id p
  map_comp := by
    intro T₁ T₂ T₃ φ ψ
    ext p
    exact Pair.restrict_comp p ψ.unop φ.unop

/-- Sections of the relative-morphism presheaf are pairs over the test scheme. -/
theorem presheaf_obj (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) :
    (presheaf g h).obj (Opposite.op T) = Pair g h T := rfl

/-- The relative-morphism presheaf acts on morphisms by restriction of pairs. -/
theorem presheaf_map (g : Z ⟶ B) (h : X ⟶ B) {T T' : Over S}
    (φ : T' ⟶ T) (p : Pair g h T) :
    (presheaf g h).map φ.op p = p.restrict φ := rfl

/-- Relative morphisms satisfy fppf descent. -/
theorem isSheaf (g : Z ⟶ B) (h : X ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (presheaf g h) := sorry

/-- The fppf sheaf of relative morphisms from `Z` to `X` over `B`. -/
def sheaf (g : Z ⟶ B) (h : X ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨presheaf g h, isSheaf g h⟩

/-- Sections of the relative-morphism sheaf are pairs over the test scheme. -/
theorem sheaf_obj (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) :
    (sheaf g h).obj.obj (Opposite.op T) = Pair g h T := rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
