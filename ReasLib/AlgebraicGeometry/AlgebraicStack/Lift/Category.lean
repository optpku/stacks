/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Object
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Comparison

/-!
# Compatible morphisms and the category of lifts of algebraic stacks

Compatible pairs of space maps with triangle isomorphisms form the morphisms
of the category of cartesian smooth lifts. Forgetting the thickened space
and its triangle cell gives a functor to the spaces-étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}}

variable {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable {iX : X ⟶ X'} [IsThickening iX]
variable {W : AlgebraicSpace S} {x : W.toGroupoids ⟶ X}
variable [Groupoids.Hom.Smooth x]

namespace Object

namespace Hom

/-- Source-leg transport for `f*α`: `(map ξ.a ≫ x) ≫ iX` is identified with
`map f ≫ ((map η.a ≫ x) ≫ iX)` by `overW`, `AlgebraicSpace.toGroupoids.mapCompIso`, and
associators. -/
def srcWhiskerIso {ξ η : Object iX x} (f : ξ.U ⟶ η.U)
    (overW : f ≫ η.a = ξ.a) :
    ((AlgebraicSpace.toGroupoids.map ξ.a ≫ x) ≫ iX) ≅
      AlgebraicSpace.toGroupoids.map f ≫
        ((AlgebraicSpace.toGroupoids.map η.a ≫ x) ≫ iX) :=
  whiskerRightIso (whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map overW.symm)) x) iX ≪≫
    whiskerRightIso (whiskerRightIso (AlgebraicSpace.toGroupoids.mapCompIso f η.a) x) iX ≪≫
    whiskerRightIso
      (α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.a) x) iX ≪≫
    α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.a ≫ x) iX

/-- Target-leg transport for `j*γ`: `map f ≫ (map η.i ≫ η.x')` is identified
with `map ξ.i ≫ ξ.x'` by `restrict`, `AlgebraicSpace.toGroupoids.mapCompIso`, associators, and
left whiskering of `γ`. -/
def tgtWhiskerIso {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x') :
    AlgebraicSpace.toGroupoids.map f ≫
        (AlgebraicSpace.toGroupoids.map η.i ≫ η.x') ≅
      AlgebraicSpace.toGroupoids.map ξ.i ≫ ξ.x' :=
  (α_ (AlgebraicSpace.toGroupoids.map f) (AlgebraicSpace.toGroupoids.map η.i) η.x').symm ≪≫
    whiskerRightIso (AlgebraicSpace.toGroupoids.mapCompIso f η.i).symm η.x' ≪≫
    whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map restrict.symm)) η.x' ≪≫
    whiskerRightIso (AlgebraicSpace.toGroupoids.mapCompIso ξ.i f') η.x' ≪≫
    α_ (AlgebraicSpace.toGroupoids.map ξ.i) (AlgebraicSpace.toGroupoids.map f') η.x' ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map ξ.i) triangle

/-- The square cell of the source lift is the pasting of the target square
cell with the source-leg and target-leg comparison isomorphisms. -/
def IsCompatible {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (overW : f ≫ η.a = ξ.a) (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x') : Prop :=
  ξ.α =
    (srcWhiskerIso f overW) ≪≫
      (whiskerLeftIso (AlgebraicSpace.toGroupoids.map f) η.α) ≪≫
        (tgtWhiskerIso f f' restrict triangle)

end Hom

/-- A compatible morphism of lifts is raw diagram data whose triangle cell
respects the square cells of its source and target. -/
def Hom (ξ η : Object iX x) : Type (u + 1) :=
  {h : AlgebraicGeometry.AlgebraicStack.Lift.Hom η.a η.i η.x' ξ.a ξ.i ξ.x' //
    Hom.IsCompatible h.f h.f' h.overW h.restrict h.triangle}

namespace Hom

/-- The map between the spaces étale over the fixed algebraic space. -/
def f {ξ η : Object iX x} (φ : Hom ξ η) : ξ.U ⟶ η.U := φ.val.f

/-- The map between the spaces smooth over the thickened stack. -/
def f' {ξ η : Object iX x} (φ : Hom ξ η) : ξ.U' ⟶ η.U' := φ.val.f'

/-- The underlying map of a compatible morphism is over the fixed space. -/
theorem overW {ξ η : Object iX x} (φ : Hom ξ η) : φ.f ≫ η.a = ξ.a := φ.val.overW

/-- The map on the thickened spaces restricts to the map on the source spaces. -/
theorem restrict {ξ η : Object iX x} (φ : Hom ξ η) :
    ξ.i ≫ φ.f' = φ.f ≫ η.i := φ.val.restrict

/-- The triangle isomorphism over the thickened stack. -/
def triangle {ξ η : Object iX x} (φ : Hom ξ η) :
    AlgebraicSpace.toGroupoids.map φ.f' ≫ η.x' ≅ ξ.x' := φ.val.triangle

/-- The triangle cell of a compatible morphism respects the lift square cells. -/
theorem compatible {ξ η : Object iX x} (φ : Hom ξ η) :
    IsCompatible φ.f φ.f' φ.overW φ.restrict φ.triangle := φ.property

/-- Space maps, face equalities, and a compatible triangle cell determine a
morphism of lifts. -/
def mk {ξ η : Object iX x} (f : ξ.U ⟶ η.U) (f' : ξ.U' ⟶ η.U')
    (overW : f ≫ η.a = ξ.a) (restrict : ξ.i ≫ f' = f ≫ η.i)
    (triangle : AlgebraicSpace.toGroupoids.map f' ≫ η.x' ≅ ξ.x')
    (compatible : IsCompatible f f' overW restrict triangle) : Hom ξ η :=
  ⟨AlgebraicGeometry.AlgebraicStack.Lift.Hom.mk f f' overW restrict triangle, compatible⟩

/-- A morphism of lifts has its first map over the fixed space, its second
map restricting to the first, and compatible square cells. -/
theorem spec {ξ η : Object iX x} (φ : Hom ξ η) :
    φ.f ≫ η.a = ξ.a ∧ ξ.i ≫ φ.f' = φ.f ≫ η.i ∧
      IsCompatible φ.f φ.f' φ.overW φ.restrict φ.triangle := sorry

/-- A morphism of lifts is reconstructed from its displayed components. -/
theorem eta {ξ η : Object iX x} (φ : Hom ξ η) :
    φ = mk φ.f φ.f' φ.overW φ.restrict φ.triangle φ.compatible := sorry

/-- Forget the square-cell compatibility of a morphism of lifts. -/
def toUnbundled {ξ η : Object iX x} (φ : Hom ξ η) :
    AlgebraicGeometry.AlgebraicStack.Lift.Hom η.a η.i η.x' ξ.a ξ.i ξ.x' := φ.val

/-- Compatible raw diagram data determines a morphism of lifts. -/
def ofUnbundled {ξ η : Object iX x}
    (h : AlgebraicGeometry.AlgebraicStack.Lift.Hom η.a η.i η.x' ξ.a ξ.i ξ.x')
    (compatible : IsCompatible h.f h.f' h.overW h.restrict h.triangle) : Hom ξ η :=
  ⟨h, compatible⟩

/-- The identity triangle is the identity comparison followed by the left unitor. -/
def idTriangle (ξ : Object iX x) :
    AlgebraicSpace.toGroupoids.map (𝟙 ξ.U') ≫ ξ.x' ≅ ξ.x' :=
  whiskerRightIso AlgebraicSpace.toGroupoids.mapIdIso ξ.x' ≪≫ λ_ ξ.x'

/-- The identity map on a lift's source space is over the fixed space. -/
theorem id_overW (ξ : Object iX x) : (𝟙 ξ.U) ≫ ξ.a = ξ.a := sorry

/-- Identity maps commute with the map between a lift's two spaces. -/
theorem id_restrict (ξ : Object iX x) :
    ξ.i ≫ (𝟙 ξ.U') = (𝟙 ξ.U) ≫ ξ.i := sorry

/-- The identity triangle respects the square cell of a lift. -/
theorem id_compatible (ξ : Object iX x) :
    IsCompatible (𝟙 ξ.U) (𝟙 ξ.U') (id_overW ξ) (id_restrict ξ)
      (idTriangle ξ) := sorry

/-- The identity morphism of a lift has identity space maps and the unitor triangle. -/
def id (ξ : Object iX x) : Hom ξ ξ :=
  mk (𝟙 ξ.U) (𝟙 ξ.U') (id_overW ξ) (id_restrict ξ) (idTriangle ξ) (id_compatible ξ)

/-- The composite triangle is obtained by the composition comparison,
associator, and whiskering of the two triangle cells. -/
def compTriangle {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) :
    AlgebraicSpace.toGroupoids.map (φ.f' ≫ ψ.f') ≫ ζ.x' ≅ ξ.x' :=
  whiskerRightIso (AlgebraicSpace.toGroupoids.mapCompIso φ.f' ψ.f') ζ.x' ≪≫
    α_ (AlgebraicSpace.toGroupoids.map φ.f') (AlgebraicSpace.toGroupoids.map ψ.f') ζ.x' ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map φ.f') ψ.triangle ≪≫ φ.triangle

/-- The composite of the source-space maps of two lift morphisms is over the fixed space. -/
theorem comp_overW {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) :
    (φ.f ≫ ψ.f) ≫ ζ.a = ξ.a := sorry

/-- The composite map on thickened spaces restricts to the composite on source spaces. -/
theorem comp_restrict {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) :
    ξ.i ≫ (φ.f' ≫ ψ.f') = (φ.f ≫ ψ.f) ≫ ζ.i := sorry

/-- Pasting compatible triangle cells gives a compatible composite triangle cell. -/
theorem comp_compatible {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) :
    IsCompatible (φ.f ≫ ψ.f) (φ.f' ≫ ψ.f') (comp_overW φ ψ) (comp_restrict φ ψ)
      (compTriangle φ ψ) := sorry

/-- Composition of lift morphisms composes the space maps and pastes their triangle cells. -/
def comp {ξ η ζ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) : Hom ξ ζ :=
  mk (φ.f ≫ ψ.f) (φ.f' ≫ ψ.f') (comp_overW φ ψ) (comp_restrict φ ψ)
    (compTriangle φ ψ) (comp_compatible φ ψ)

/-- The identity lift morphism is a left identity for composition. -/
theorem id_comp {ξ η : Object iX x} (φ : Hom ξ η) : comp (id ξ) φ = φ := sorry

/-- The identity lift morphism is a right identity for composition. -/
theorem comp_id {ξ η : Object iX x} (φ : Hom ξ η) : comp φ (id η) = φ := sorry

/-- Composition of compatible lift morphisms is associative. -/
theorem assoc {ξ η ζ τ : Object iX x} (φ : Hom ξ η) (ψ : Hom η ζ) (χ : Hom ζ τ) :
    comp (comp φ ψ) χ = comp φ (comp ψ χ) := sorry

end Hom

end Object

/-- Lifts of a smooth algebraic space along a thickening of algebraic stacks
form a category with compatible diagram morphisms. -/
instance category (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Category.{u + 1} (Object iX x) where
  Hom := Object.Hom
  id := Object.Hom.id
  comp := Object.Hom.comp
  id_comp := Object.Hom.id_comp
  comp_id := Object.Hom.comp_id
  assoc := Object.Hom.assoc

/-- The source-space map of an identity lift morphism is an identity in the étale site. -/
theorem p_map_id (ξ : Object iX x) :
    (MorphismProperty.Over.homMk (Object.Hom.id ξ).f (Object.Hom.id ξ).overW :
      ξ.toSpacesEtale ⟶ ξ.toSpacesEtale) = 𝟙 ξ.toSpacesEtale := sorry

/-- The source-space map of a composite lift morphism is the composite in the étale site. -/
theorem p_map_comp {ξ η ζ : Object iX x} (φ : Object.Hom ξ η) (ψ : Object.Hom η ζ) :
    (MorphismProperty.Over.homMk (Object.Hom.comp φ ψ).f
      (Object.Hom.comp φ ψ).overW : ξ.toSpacesEtale ⟶ ζ.toSpacesEtale) =
      (MorphismProperty.Over.homMk φ.f φ.overW : ξ.toSpacesEtale ⟶ η.toSpacesEtale) ≫
        (MorphismProperty.Over.homMk ψ.f ψ.overW : η.toSpacesEtale ⟶ ζ.toSpacesEtale) := sorry

/-- The forgetful functor sends a lift to its étale structure map over the fixed space. -/
def p (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    Object iX x ⥤ AlgebraicSpace.spacesEtaleSite W where
  obj ξ := ξ.toSpacesEtale
  map φ := MorphismProperty.Over.homMk φ.f φ.overW
  map_id := p_map_id
  map_comp := p_map_comp

/-- The object part of the forgetful functor is the lift's étale structure map. -/
theorem p_obj (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] (ξ : Object iX x) :
    (p iX x).obj ξ = ξ.toSpacesEtale := sorry

/-- The morphism part of the forgetful functor is the underlying map over the fixed space. -/
theorem p_map (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x]
    {ξ η : Object iX x} (φ : ξ ⟶ η) :
    (p iX x).map φ = MorphismProperty.Over.homMk φ.f φ.overW := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
