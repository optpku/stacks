/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Boolean
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Data.ZMod.Basic

/-! # Algebra operations on finite-part sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The first factor of a compatible pair of finite-part sections over `Y`. -/
def starFst {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    FinitePart.Point f T.unop :=
  (pullback.fst (finitePartTo f) (finitePartTo f)).hom.app T s

/-- The second factor of a compatible pair of finite-part sections over `Y`. -/
def starSnd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    FinitePart.Point f T.unop :=
  (pullback.snd (finitePartTo f) (finitePartTo f)).hom.app T s

/-- Compatible pairs in the self-fibre product over `Y` have the same morphism `a`. -/
theorem star_a_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (starFst f T s).a = (starSnd f T s).a :=
  sorry

/-- Union of compatible finite-part pairs commutes with restriction. -/
theorem star1_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (finitePartTo f) (finitePartTo f)).obj.map g ≫
        TypeCat.ofHom (fun s ↦ (starFst f T' s).union (starSnd f T' s) (star_a_eq f T' s)) =
      TypeCat.ofHom (fun s ↦ (starFst f T s).union (starSnd f T s) (star_a_eq f T s)) ≫ (finitePartSheaf f).obj.map g :=
  sorry

/-- Union of compatible finite-part pairs as a morphism of sheaves. -/
def star1 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ (starFst f T s).union (starSnd f T s) (star_a_eq f T s)
      naturality := fun _ _ g ↦ star1_naturality f g }

/-- The components of union are the corresponding operations on finite-part pairs. -/
theorem star1_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star1 f).hom.app T s =
      (starFst f T s).union (starSnd f T s) (star_a_eq f T s) :=
  rfl

/-- Intersection of compatible finite-part pairs commutes with restriction. -/
theorem star2_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (finitePartTo f) (finitePartTo f)).obj.map g ≫
        TypeCat.ofHom (fun s ↦ (starFst f T' s).inter (starSnd f T' s) (star_a_eq f T' s)) =
      TypeCat.ofHom (fun s ↦ (starFst f T s).inter (starSnd f T s) (star_a_eq f T s)) ≫ (finitePartSheaf f).obj.map g :=
  sorry

/-- Intersection of compatible finite-part pairs as a morphism of sheaves. -/
def star2 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ (starFst f T s).inter (starSnd f T s) (star_a_eq f T s)
      naturality := fun _ _ g ↦ star2_naturality f g }

/-- The components of intersection are the corresponding operations on finite-part pairs. -/
theorem star2_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star2 f).hom.app T s =
      (starFst f T s).inter (starSnd f T s) (star_a_eq f T s) :=
  rfl

/-- Set-difference of compatible finite-part pairs commutes with restriction. -/
theorem star3_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (finitePartTo f) (finitePartTo f)).obj.map g ≫
        TypeCat.ofHom (fun s ↦ (starFst f T' s).sdiff (starSnd f T' s) (star_a_eq f T' s)) =
      TypeCat.ofHom (fun s ↦ (starFst f T s).sdiff (starSnd f T s) (star_a_eq f T s)) ≫ (finitePartSheaf f).obj.map g :=
  sorry

/-- Set-difference of compatible finite-part pairs as a morphism of sheaves. -/
def star3 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ (starFst f T s).sdiff (starSnd f T s) (star_a_eq f T s)
      naturality := fun _ _ g ↦ star3_naturality f g }

/-- The components of set-difference are the corresponding operations on finite-part pairs. -/
theorem star3_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star3 f).hom.app T s =
      (starFst f T s).sdiff (starSnd f T s) (star_a_eq f T s) :=
  rfl

/-- Reversed set-difference of compatible finite-part pairs commutes with restriction. -/
theorem star4_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (finitePartTo f) (finitePartTo f)).obj.map g ≫
        TypeCat.ofHom (fun s ↦ (starSnd f T' s).sdiff (starFst f T' s) (star_a_eq f T' s).symm) =
      TypeCat.ofHom (fun s ↦ (starSnd f T s).sdiff (starFst f T s) (star_a_eq f T s).symm) ≫ (finitePartSheaf f).obj.map g :=
  sorry

/-- Reversed set-difference of compatible finite-part pairs as a morphism of sheaves. -/
def star4 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ (starSnd f T s).sdiff (starFst f T s) (star_a_eq f T s).symm
      naturality := fun _ _ g ↦ star4_naturality f g }

/-- The components of reversed set-difference are the corresponding operations on finite-part pairs. -/
theorem star4_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star4 f).hom.app T s =
      (starSnd f T s).sdiff (starFst f T s) (star_a_eq f T s).symm :=
  rfl

/-- Symmetric difference of compatible finite-part pairs commutes with restriction. -/
theorem finitePartAdd_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (finitePartTo f) (finitePartTo f)).obj.map g ≫
        TypeCat.ofHom (fun s ↦ (starFst f T' s).add (starSnd f T' s) (star_a_eq f T' s)) =
      TypeCat.ofHom (fun s ↦ (starFst f T s).add (starSnd f T s) (star_a_eq f T s)) ≫ (finitePartSheaf f).obj.map g :=
  sorry

/-- Symmetric difference of compatible finite-part pairs as a morphism of sheaves. -/
def finitePartAdd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ (starFst f T s).add (starSnd f T s) (star_a_eq f T s)
      naturality := fun _ _ g ↦ finitePartAdd_naturality f g }

/-- The components of symmetric difference are the corresponding operations on finite-part pairs. -/
theorem finitePartAdd_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (finitePartAdd f).hom.app T s =
      (starFst f T s).add (starSnd f T s) (star_a_eq f T s) :=
  rfl

/-- Union preserves the structure morphism to the base. -/
theorem star1_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    star1 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Intersection preserves the structure morphism to the base. -/
theorem star2_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    star2 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Set-difference preserves the structure morphism to the base. -/
theorem star3_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    star3 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Reversed set-difference preserves the structure morphism to the base. -/
theorem star4_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    star4 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Symmetric difference preserves the structure morphism to the base. -/
theorem finitePartAdd_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    finitePartAdd f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- The empty finite-part pair commutes with restriction of base sections. -/
theorem finitePartZero_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    ((toFppfSheaf S).obj Y).obj.map g ≫
        TypeCat.ofHom (fun y ↦ (FinitePart.Point.empty (yonedaEquiv.symm (ULift.down y)) : FinitePart.Point f T'.unop)) =
      TypeCat.ofHom (fun y ↦ (FinitePart.Point.empty (yonedaEquiv.symm (ULift.down y)) : FinitePart.Point f T.unop)) ≫
        (finitePartSheaf f).obj.map g :=
  sorry

/-- The section assigning the empty open in each fibre. -/
def finitePartZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (toFppfSheaf S).obj Y ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun y ↦ FinitePart.Point.empty (yonedaEquiv.symm (ULift.down y))
      naturality := fun _ _ g ↦ finitePartZero_naturality f g }

/-- The section of empty opens has the specified finite-part pair as its component. -/
theorem finitePartZero_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T) :
    (finitePartZero f).hom.app T y = FinitePart.Point.empty (yonedaEquiv.symm (ULift.down y)) :=
  rfl

/-- The section of empty opens is a section of the structure morphism. -/
theorem finitePartZero_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    finitePartZero f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y) :=
  sorry

/-- The whole finite-part pair commutes with restriction of base sections. -/
theorem finitePartOne_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    ((toFppfSheaf S).obj Y).obj.map g ≫
        TypeCat.ofHom (fun y ↦ (FinitePart.Point.univ (yonedaEquiv.symm (ULift.down y)) : FinitePart.Point f T'.unop)) =
      TypeCat.ofHom (fun y ↦ (FinitePart.Point.univ (yonedaEquiv.symm (ULift.down y)) : FinitePart.Point f T.unop)) ≫
        (finitePartSheaf f).obj.map g :=
  sorry

/-- The section assigning the whole open in each fibre. -/
def finitePartOne {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f] :
    (toFppfSheaf S).obj Y ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun y ↦ FinitePart.Point.univ (yonedaEquiv.symm (ULift.down y))
      naturality := fun _ _ g ↦ finitePartOne_naturality f g }

/-- The section of whole opens has the specified finite-part pair as its component. -/
theorem finitePartOne_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T) :
    (finitePartOne f).hom.app T y = FinitePart.Point.univ (yonedaEquiv.symm (ULift.down y)) :=
  rfl

/-- The section of whole opens is a section of the structure morphism. -/
theorem finitePartOne_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f] :
    finitePartOne f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y) :=
  sorry

namespace FinitePart

/-- Finite-part pairs over a fixed morphism from a test scheme to the base. -/
def Fiber {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {T : Over S} (a : ofOver T ⟶ Y) : Type (u + 1) :=
  {p : Point f T // p.a = a}

namespace Fiber

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {T : Over S} {a : ofOver T ⟶ Y}

/-- The empty finite-part pair in a fixed fibre. -/
def zero (f : X ⟶ Y) (a : ofOver T ⟶ Y) : Fiber f a :=
  ⟨Point.empty a, rfl⟩

/-- The whole finite-part pair in a fixed fibre of a finite morphism. -/
def one (f : X ⟶ Y) [IsFinite f] (a : ofOver T ⟶ Y) : Fiber f a :=
  ⟨Point.univ a, rfl⟩

/-- Union of two finite-part pairs in the same fibre. -/
def union [Separated f] (p q : Fiber f a) : Fiber f a :=
  ⟨p.val.union q.val (p.property.trans q.property.symm), p.property⟩

/-- Difference of two finite-part pairs in the same fibre. -/
def sdiff [Separated f] (p q : Fiber f a) : Fiber f a :=
  ⟨p.val.sdiff q.val (p.property.trans q.property.symm), p.property⟩

/-- Addition in a fixed fibre is symmetric difference of finite-part opens. -/
def add [Separated f] (p q : Fiber f a) : Fiber f a :=
  ⟨p.val.add q.val (p.property.trans q.property.symm), p.property⟩

/-- Multiplication in a fixed fibre is intersection of finite-part opens. -/
def mul [Separated f] (p q : Fiber f a) : Fiber f a :=
  ⟨p.val.inter q.val (p.property.trans q.property.symm), p.property⟩

/-- The scalar action of the field with two elements is zero or the identity. -/
def smul (c : ZMod 2) (p : Fiber f a) : Fiber f a :=
  if c = 0 then zero f a else p

/-- Restriction of a finite-part pair to a test scheme over the original test scheme. -/
def restrict (p : Fiber f a) {T' : Over S} (h : T' ⟶ T) :
    Fiber f (ofOverMap h ≫ a) :=
  ⟨p.val.restrict h, congrArg (fun b ↦ ofOverMap h ≫ b) p.property⟩

end Fiber
end FinitePart

open FinitePart

/-- Symmetric difference, intersection and the zero-or-identity scalar action give
finite-part fibres commutative idempotent non-unital algebras over the field with
two elements, and restriction preserves these operations. -/
theorem finitePartAlgebraLaws {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] :
    ∀ (T : Over S) (a : ofOver T ⟶ Y),
      (∀ (p q r : Fiber f a),
        Fiber.add (Fiber.add p q) r = Fiber.add p (Fiber.add q r) ∧
        Fiber.add p q = Fiber.add q p ∧
        Fiber.add (Fiber.zero f a) p = p ∧
        Fiber.add p (Fiber.zero f a) = p ∧
        Fiber.add p p = Fiber.zero f a ∧
        Fiber.mul (Fiber.mul p q) r = Fiber.mul p (Fiber.mul q r) ∧
        Fiber.mul p q = Fiber.mul q p ∧
        Fiber.mul (Fiber.zero f a) p = Fiber.zero f a ∧
        Fiber.mul p (Fiber.zero f a) = Fiber.zero f a ∧
        Fiber.mul p (Fiber.add q r) = Fiber.add (Fiber.mul p q) (Fiber.mul p r) ∧
        Fiber.mul (Fiber.add p q) r = Fiber.add (Fiber.mul p r) (Fiber.mul q r) ∧
        Fiber.mul p p = p ∧
        Fiber.add p q = Fiber.union (Fiber.sdiff p q) (Fiber.sdiff q p)) ∧
      (∀ (c d : ZMod 2) (p q : Fiber f a),
        Fiber.smul 1 p = p ∧
        Fiber.smul 0 p = Fiber.zero f a ∧
        Fiber.smul c (Fiber.zero f a) = Fiber.zero f a ∧
        Fiber.smul (c * d) p = Fiber.smul c (Fiber.smul d p) ∧
        Fiber.smul (c + d) p = Fiber.add (Fiber.smul c p) (Fiber.smul d p) ∧
        Fiber.smul c (Fiber.add p q) = Fiber.add (Fiber.smul c p) (Fiber.smul c q) ∧
        Fiber.smul c (Fiber.mul p q) = Fiber.mul (Fiber.smul c p) q ∧
        Fiber.smul c (Fiber.mul p q) = Fiber.mul p (Fiber.smul c q)) ∧
      (∀ (T' : Over S) (h : T' ⟶ T) (p q : Fiber f a) (c : ZMod 2),
        Fiber.restrict (Fiber.zero f a) h = Fiber.zero f (ofOverMap h ≫ a) ∧
        Fiber.restrict (Fiber.add p q) h =
          Fiber.add (Fiber.restrict p h) (Fiber.restrict q h) ∧
        Fiber.restrict (Fiber.mul p q) h =
          Fiber.mul (Fiber.restrict p h) (Fiber.restrict q h) ∧
        Fiber.restrict (Fiber.smul c p) h = Fiber.smul c (Fiber.restrict p h)) :=
  sorry

/-- For a finite separated morphism, whole fibres are multiplicative units,
restriction preserves them, and differences are products with complements. -/
theorem finitePartUnitLaws {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] [IsFinite f] :
    ∀ (T : Over S) (a : ofOver T ⟶ Y),
      (∀ (p q : Fiber f a),
        Fiber.mul (Fiber.one f a) p = p ∧
        Fiber.mul p (Fiber.one f a) = p ∧
        Fiber.sdiff p q = Fiber.mul p (Fiber.add (Fiber.one f a) q) ∧
        Fiber.sdiff q p = Fiber.mul (Fiber.add (Fiber.one f a) p) q) ∧
      (∀ (T' : Over S) (h : T' ⟶ T),
        Fiber.restrict (Fiber.one f a) h = Fiber.one f (ofOverMap h ≫ a)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
