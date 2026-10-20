/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap106.«106_6_1_1_Object»
public import stacks_project.Chap106.«106_6_1_2_Hom»

/-!
# The category of lifts along a thickening of algebraic stacks

Objects are systems `(U, U', a, i, x', α)` as in `Object`. Morphisms are
triples `(f, f', γ)` over `W` with `f'` restricting to `f`, together with the
compatibility `β = j*γ ∘ f*α`. The forgetful functor `p` sends a lift to its
étale structure map in `W_spaces,étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}}

/-- The identity comparison for `AlgebraicSpace.toGroupoids.map`, obtained from
the `map_id` fields of `Sets.ofPresheaf` and `Sets.toGroupoids`. -/
def toGroupoidsMapIdIso {U : AlgebraicSpace S} :
    AlgebraicSpace.toGroupoids.map (𝟙 U) ≅ 𝟙 U.toGroupoids :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map_id U.functorOfPoints)).trans
      ((Sets.toGroupoids (Over S)).map_id
        ((Sets.ofPresheaf (Over S)).obj U.functorOfPoints))

/-- The composition comparison for `AlgebraicSpace.toGroupoids.map`, obtained
from the `map_comp` fields of `Sets.ofPresheaf` and `Sets.toGroupoids`. -/
def toGroupoidsMapCompIso {U V W : AlgebraicSpace S} (f : U ⟶ V) (g : V ⟶ W) :
    AlgebraicSpace.toGroupoids.map (f ≫ g) ≅
      AlgebraicSpace.toGroupoids.map f ≫ AlgebraicSpace.toGroupoids.map g :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map_comp f g)).trans
      ((Sets.toGroupoids (Over S)).map_comp
        ((Sets.ofPresheaf (Over S)).map f) ((Sets.ofPresheaf (Over S)).map g))

/-- Transport `AlgebraicSpace.toGroupoids.map` along an equality of algebraic-space
morphisms. -/
def toGroupoidsMapCongrIso {U V : AlgebraicSpace S} {f g : U ⟶ V} (h : f = g) :
    AlgebraicSpace.toGroupoids.map f ≅ AlgebraicSpace.toGroupoids.map g :=
  eqToIso (congrArg AlgebraicSpace.toGroupoids.map h)

variable {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable {iX : X ⟶ X'} [IsThickening iX]
variable {W : AlgebraicSpace S} {x : W.toGroupoids ⟶ X}
variable [Groupoids.Hom.Smooth x]

namespace Object

namespace Hom

/-- Source-leg transport for `f*α`: `(map ξ.a ≫ x) ≫ iX` is identified with
`map f ≫ ((map η.a ≫ x) ≫ iX)` by `overW`, `toGroupoidsMapCompIso`, and
associators. -/
def srcWhiskerIso {ξ η : Object iX x} (f : ξ.U ⟶ η.U)
    (overW : f ≫ η.a = ξ.a) :
    ((AlgebraicSpace.toGroupoids.map ξ.a ≫ x) ≫ iX) ≅
      AlgebraicSpace.toGroupoids.map f ≫
        ((AlgebraicSpace.toGroupoids.map η.a ≫ x) ≫ iX) :=
  whiskerRightIso (whiskerRightIso (toGroupoidsMapCongrIso overW.symm) x) iX ≪≫
    whiskerRightIso (whiskerRightIso (toGroupoidsMapCompIso f η.a) x) iX ≪≫
    whiskerRightIso
      (α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.a) x) iX ≪≫
    α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.a ≫ x) iX

/-- Target-leg transport for `j*γ`: `map f ≫ (map η.i ≫ η.x')` is identified
with `map ξ.i ≫ ξ.x'` by `restrict`, `toGroupoidsMapCompIso`, associators, and
left whiskering of `γ`. -/
def tgtWhiskerIso {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x') :
    AlgebraicSpace.toGroupoids.map f ≫
        (AlgebraicSpace.toGroupoids.map η.i ≫ η.x') ≅
      AlgebraicSpace.toGroupoids.map ξ.i ≫ ξ.x' :=
  (α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.i) η.x').symm ≪≫
    whiskerRightIso (toGroupoidsMapCompIso f η.i).symm η.x' ≪≫
    whiskerRightIso (toGroupoidsMapCongrIso restrict.symm) η.x' ≪≫
    whiskerRightIso (toGroupoidsMapCompIso ξ.i f') η.x' ≪≫
    α_ (AlgebraicSpace.toGroupoids.map ξ.i) (AlgebraicSpace.toGroupoids.map f') η.x' ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map ξ.i) triangle

/-- Compatibility `β = j*γ ∘ f*α` of a morphism of lifts: the square 2-cell of
the source object equals the pasting of `f*α` with `j*γ`, after associators and
`toGroupoids.map` transports along `overW` and `restrict`. Lean Hom direction
is `f : ξ.U ⟶ η.U`, matching the displayed diagram and `spacesEtaleSite`
rather than the remark's swapped prose labels `(U, …) → (V, …)`. -/
def IsCompatible {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (overW : f ≫ η.a = ξ.a) (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x') : Prop :=
  ξ.α =
    (srcWhiskerIso f overW) ≪≫
      (whiskerLeftIso (AlgebraicSpace.toGroupoids.map f) η.α) ≪≫
        (tgtWhiskerIso f f' restrict triangle)

end Hom

/-- A morphism of lifts `ξ ⟶ η` is a pair of algebraic-space maps `(f, f')`
together with a right-triangle 2-cell `γ` and the compatibility
`β = j*γ ∘ f*α`. The map `f` goes `ξ.U ⟶ η.U`, as in the displayed diagram
106.6.1.2 and the étale site of `W`. -/
structure Hom (ξ η : Object iX x) where
  /-- Package the space maps, triangle 2-cell, and compatibility as a morphism
  of lifts. -/
  of ::
  /-- The morphism of algebraic spaces `f : ξ.U ⟶ η.U` over `W`. -/
  f : ξ.U ⟶ η.U
  /-- The morphism of algebraic spaces `f' : ξ.U' ⟶ η.U'` restricting to `f`. -/
  f' : ξ.U' ⟶ η.U'
  /-- `f` is a morphism over `W`. -/
  overW : f ≫ η.a = ξ.a
  /-- The restriction of `f'` along `ξ.i` is `f` along `η.i`. -/
  restrict : ξ.i ≫ f' = f ≫ η.i
  /-- The 2-cell `γ : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x'` of the
  right triangle. -/
  triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x'
  /-- Compatibility `ξ.α = j*γ ∘ f*η.α`. -/
  compatible : Hom.IsCompatible f f' overW restrict triangle

namespace Hom

/-- Package space maps `f`, `f'`, the right-triangle 2-cell, and compatibility
as a morphism of lifts. -/
def mk {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (overW : f ≫ η.a = ξ.a) (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x')
    (compatible : IsCompatible f f' overW restrict triangle) :
    Hom ξ η :=
  of f f' overW restrict triangle compatible

/-- A morphism of lifts has `f` over `W`, `f'` restricting to `f`, and
compatible square 2-cells. -/
theorem spec {ξ η : Object iX x} (φ : Hom ξ η) :
    φ.f ≫ η.a = ξ.a ∧ ξ.i ≫ φ.f' = φ.f ≫ η.i ∧
      IsCompatible φ.f φ.f' φ.overW φ.restrict φ.triangle := sorry

/-- A morphism of lifts is reconstructed from its space maps, space-face
equalities, right-triangle 2-cell, and compatibility. -/
theorem iff {ξ η : Object iX x} (φ : Hom ξ η) :
    φ = mk φ.f φ.f' φ.overW φ.restrict φ.triangle φ.compatible := sorry

/-- View a bundled morphism of lifts as the unbundled displayed data of
106.6.1.2. -/
def toUnbundled {ξ η : Object iX x} (φ : Hom ξ η) :
    AlgebraicGeometry.AlgebraicStack.Lift.Hom η.a η.i η.x' ξ.a ξ.i ξ.x' :=
  AlgebraicGeometry.AlgebraicStack.Lift.Hom.mk φ.f φ.f' φ.overW φ.restrict φ.triangle

/-- Bundle unbundled 106.6.1.2 data together with compatibility as a morphism
of the category of lifts. -/
def ofUnbundled {ξ η : Object iX x}
    (h : AlgebraicGeometry.AlgebraicStack.Lift.Hom η.a η.i η.x' ξ.a ξ.i ξ.x')
    (compatible : IsCompatible h.f h.f' h.overW h.restrict h.triangle) :
    Hom ξ η :=
  mk h.f h.f' h.overW h.restrict h.triangle compatible

/-- The identity morphism of a lift uses identity space maps and the left
unitor of `x'` after `toGroupoidsMapIdIso`. -/
def id (ξ : Object iX x) : Hom ξ ξ :=
  mk (𝟙 ξ.U) (𝟙 ξ.U') sorry sorry
    (whiskerRightIso toGroupoidsMapIdIso ξ.x' ≪≫ λ_ ξ.x') sorry

/-- Composition of morphisms of lifts is composition of space maps, with the
composite triangle obtained from `toGroupoidsMapCompIso`, the associator, and
whiskering. -/
def comp {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) : Hom ξ ζ :=
  mk (φ.f ≫ ψ.f) (φ.f' ≫ ψ.f') sorry sorry
    (whiskerRightIso (toGroupoidsMapCompIso φ.f' ψ.f') ζ.x' ≪≫
      α_ (AlgebraicSpace.toGroupoids.map φ.f') (AlgebraicSpace.toGroupoids.map ψ.f')
        ζ.x' ≪≫
      whiskerLeftIso (AlgebraicSpace.toGroupoids.map φ.f') ψ.triangle ≪≫ φ.triangle)
    sorry

end Hom

end Object

/-- Lifts along a thickening `iX` of a smooth map `x` form a category, with
morphisms the bundled compatible triples `(f, f', γ)`. -/
instance category (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Category.{u + 1} (Object iX x) where
  Hom := Object.Hom
  id := Object.Hom.id
  comp := Object.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor from the category of lifts to `W_spaces,étale`,
sending a lift to its étale structure map `a : U ⟶ W`. -/
def p (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Object iX x ⥤ AlgebraicSpace.spacesEtaleSite W where
  obj ξ := ξ.toSpacesEtale
  map φ := MorphismProperty.Over.homMk φ.f φ.overW
  map_id := sorry
  map_comp := sorry

/-- The object part of `p` is the étale map `a : U ⟶ W` of the lift. -/
theorem p_obj (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] (ξ : Object iX x) :
    (p iX x).obj ξ = ξ.toSpacesEtale := sorry

/-- The morphism part of `p` is the underlying map over `W`. -/
theorem p_map (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x]
    {ξ η : Object iX x} (φ : ξ ⟶ η) :
    (p iX x).map φ = MorphismProperty.Over.homMk φ.f φ.overW := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
