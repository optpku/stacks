/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic

/-!
# Flat first-order lifts of scheme morphisms

A flat lift of a flat morphism `f : X ⟶ S` across a first-order thickening
`t : S ⟶ S'` is a pair `(f' : X' ⟶ S', a : X ≅ X' ×_{S'} S)` with `f'` flat
and `a` over `S`. The cartesian packaging is an `IsPullback` square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Thickening

open AlgebraicGeometry.RingedSpace.Thickening (kernelMapOf Solution)
open AlgebraicGeometry.RingedSpace.Hom (idealModule conormalSheaf
  pullbackPushforwardAdjunction)

variable {S S' X : Scheme.{u}}

/-- Inverse image of the conormal sheaf of a first-order thickening `t : S ⟶ S'`
along a morphism `f : X ⟶ S`. -/
abbrev pulledConormal (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) :
    X.toRingedSpace.Modules :=
  (RingedSpace.Hom.pullback f.toShHom).obj (conormalSheaf t.toShHom)

/-- The standard `f`-map `𝒞_{S/S'} ⟶ f_* (f^* 𝒞_{S/S'})` of the first-order
deformation equation. -/
def canonicalKernelMap (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) :
    idealModule t.toShHom ⟶ (RingedSpace.Hom.pushforward f.toShHom).obj (pulledConormal t f) :=
  (conormalIdealIso t).inv ≫
    (pullbackPushforwardAdjunction f.toShHom).unit.app (conormalSheaf t.toShHom)

/-- `canonicalKernelMap` is the adjunction unit of `f^* ⊣ f_*` after identifying
the kernel of `t` with its conormal sheaf. -/
theorem canonicalKernelMap_spec (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) :
    canonicalKernelMap t f =
      (conormalIdealIso t).inv ≫
        (pullbackPushforwardAdjunction f.toShHom).unit.app (conormalSheaf t.toShHom) := rfl

/-- Ext¹ of the naive cotangent complex of `f` against `f^* 𝒞_{S/S'}[0]` in
`D(𝒪_X-Mod)`. -/
abbrev extOneNL (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :=
  Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom],
    (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj (pulledConormal t f)))

/-- Ext⁰ of the naive cotangent complex of `f` against `f^* 𝒞_{S/S'}[0]` in
`D(𝒪_X-Mod)`. -/
abbrev extZeroNL (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :=
  Ext⁽(0 : ℤ)⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom],
    (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj (pulledConormal t f)))

/-- A flat first-order lift of `f : X ⟶ S` across a first-order thickening
`t : S ⟶ S'`: a flat ambient morphism `f' : X' ⟶ S'` whose closed fibre is
`S`-isomorphic to `X`. -/
structure FlatLift (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] where
  /-- The ambient scheme `X'` of the lift. -/
  space : Scheme.{u}
  /-- The ambient morphism `f' : X' ⟶ S'`. -/
  f' : space ⟶ S'
  /-- The ambient morphism is flat. -/
  flat : Flat f'
  /-- The closed-fibre morphism `i : X ⟶ X'`. -/
  i : X ⟶ space
  /-- The square with `f`, `i`, `t`, and `f'` is cartesian. -/
  isPullback : IsPullback f i t f'

namespace FlatLift

variable {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S} [Flat f]

/-- Assemble a flat lift from an ambient morphism, a closed-fibre morphism, and a
cartesian square. -/
def of {X' : Scheme.{u}} (f' : X' ⟶ S') [Flat f'] (i : X ⟶ X')
    (isPullback : IsPullback f i t f') : FlatLift t f where
  space := X'
  f' := f'
  flat := inferInstance
  i := i
  isPullback := isPullback

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The specified closed-fibre isomorphism yields a commutative square. -/
private theorem ofIso_comm {X' : Scheme.{u}} (f' : X' ⟶ S') [Flat f']
    (a : X ≅ pullback f' t) (over : a.hom ≫ pullback.snd f' t = f) :
    (a.hom ≫ pullback.fst f' t) ≫ f' = f ≫ t := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- A flat lift determined by a pair `(f' : X' ⟶ S', a : X ≅ X' ×_{S'} S)`
over `S`. -/
def ofIso {X' : Scheme.{u}} (f' : X' ⟶ S') [Flat f']
    (a : X ≅ pullback f' t) (over : a.hom ≫ pullback.snd f' t = f) :
    FlatLift t f :=
  of f' (a.hom ≫ pullback.fst f' t)
    (IsPullback.flip (IsPullback.of_iso_pullback { w := ofIso_comm f' a over } a rfl over))

/-- The commutative square of a flat lift. -/
theorem sq (L : FlatLift t f) : CommSq f L.i t L.f' :=
  L.isPullback.toCommSq

/-- The specified isomorphism `a : X ≅ X' ×_{S'} S` with the closed fibre of a flat lift. -/
def iso (L : FlatLift t f) : X ≅ pullback L.f' t :=
  L.isPullback.flip.isoPullback

/-- The isomorphism `L.iso` is over `S`. -/
theorem iso_over (L : FlatLift t f) :
    L.iso.hom ≫ pullback.snd L.f' t = f := sorry

/-- The closed-fibre morphism of a flat lift is a first-order thickening. -/
theorem i_isFirstOrder (L : FlatLift t f) : IsFirstOrderThickening L.i := sorry

/-- A flat lift has a flat ambient morphism, a cartesian square, and a first-order
closed-fibre thickening. -/
theorem spec (L : FlatLift t f) :
    Flat L.f' ∧ IsPullback f L.i t L.f' ∧ IsFirstOrderThickening L.i :=
  ⟨L.flat, L.isPullback, i_isFirstOrder L⟩

/-- The scheme-level conormal comparison of a flat lift is an isomorphism. -/
theorem conormalMap_isIso (L : FlatLift t f) :
    IsIso (Scheme.Hom.Conormal.map L.sq) := sorry

/-- The underlying square of ringed spaces of a flat lift. -/
theorem sqSh (L : FlatLift t f) :
    CommSq f.toShHom L.i.toShHom t.toShHom L.f'.toShHom := sorry

/-- The ringed-space conormal comparison of a flat lift is an isomorphism. -/
theorem conormalMapSh_isIso (L : FlatLift t f) :
    IsIso (RingedSpace.Hom.Conormal.map L.sqSh) := sorry

/-- Identification of `Ker(i^♯)` with `f^* 𝒞_{S/S'}` from the cartesian flat square. -/
def kernelIso (L : FlatLift t f) :
    idealModule L.i.toShHom ≅ pulledConormal t f :=
  (@conormalIdealIso _ _ L.i (i_isFirstOrder L)).symm ≪≫
    (@asIso _ _ _ _ (RingedSpace.Hom.Conormal.map L.sqSh) (conormalMapSh_isIso L)).symm

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The underlying ringed-space square of a lift commutes. -/
private theorem toSolution_comm (L : FlatLift t f) :
    L.i.toShHom ≫ L.f'.toShHom = f.toShHom ≫ t.toShHom := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The canonical kernel identification induces the adjunction-unit coefficient map. -/
private theorem toSolution_induces (L : FlatLift t f) :
    kernelMapOf t.toShHom f.toShHom L.i.toShHom
      (@instIsFirstOrderThickening_toShHom _ _ L.i (i_isFirstOrder L))
      L.f'.toShHom (toSolution_comm L) ≫
        (RingedSpace.Hom.pushforward f.toShHom).map (kernelIso L).hom =
      canonicalKernelMap t f := sorry

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- The underlying ringed-space solution of a flat lift has its canonical pulled
conormal kernel identification. -/
def toSolution (L : FlatLift t f) :
    Solution t.toShHom f.toShHom (pulledConormal t f) (canonicalKernelMap t f) where
  space := L.space.toRingedSpace
  i := L.i.toShHom
  i_isFirstOrder := @instIsFirstOrderThickening_toShHom _ _ L.i (i_isFirstOrder L)
  f' := L.f'.toShHom
  commutes := toSolution_comm L
  kernelIso := kernelIso L
  induces_c := toSolution_induces L

/-- `toSolution` uses the closed-fibre thickening of `L` and the kernel identification
`kernelIso L`. -/
theorem toSolution_spec (L : FlatLift t f) :
    (toSolution L).i = L.i.toShHom ∧ (toSolution L).f' = L.f'.toShHom ∧
      (toSolution L).kernelIso = kernelIso L := ⟨rfl, rfl, rfl⟩

/-- Morphisms of flat lifts: an isomorphism of ambient schemes over `S'` reducing to
the identity on the closed fibre `X`. -/
structure Hom (L₁ L₂ : FlatLift t f) where
  /-- The underlying morphism of ambient schemes. -/
  hom : L₁.space ⟶ L₂.space
  /-- The morphism is over `S'`. -/
  over : hom ≫ L₂.f' = L₁.f'
  /-- The morphism reduces to the identity on `X`. -/
  restrict : L₁.i ≫ hom = L₂.i
  /-- The underlying morphism is an isomorphism. -/
  isIso : IsIso hom

namespace Hom

/-- Assemble a morphism of flat lifts from an isomorphism of ambient schemes compatible
with `f'` and `i`. -/
def of {L₁ L₂ : FlatLift t f} (hom : L₁.space ⟶ L₂.space)
    (over : hom ≫ L₂.f' = L₁.f') (restrict : L₁.i ≫ hom = L₂.i)
    [IsIso hom] : Hom L₁ L₂ where
  hom := hom
  over := over
  restrict := restrict
  isIso := inferInstance

/-- A morphism of flat lifts is over `S'`, reduces to `id` on `X`, and is an
isomorphism. -/
theorem spec {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    φ.hom ≫ L₂.f' = L₁.f' ∧ L₁.i ≫ φ.hom = L₂.i ∧ IsIso φ.hom := ⟨φ.over, φ.restrict, φ.isIso⟩

/-- The identity isomorphism of a flat lift. -/
def id (L : FlatLift t f) : Hom L L where
  hom := 𝟙 L.space
  over := Category.id_comp L.f'
  restrict := Category.comp_id L.i
  isIso := inferInstance

/-- Composition of compatible ambient isomorphisms of flat lifts. -/
def comp {L₁ L₂ L₃ : FlatLift t f} (φ : Hom L₁ L₂) (ψ : Hom L₂ L₃) :
    Hom L₁ L₃ where
  hom := φ.hom ≫ ψ.hom
  over := by rw [Category.assoc, ψ.over, φ.over]
  restrict := by rw [← Category.assoc, φ.restrict, ψ.restrict]
  isIso := IsIso.comp_isIso' φ.isIso ψ.isIso

end Hom

/-- Automorphisms of a given flat lift over `S'` which reduce to the identity on the
closed fibre `X ≅ X' ×_{S'} S`. -/
structure ReduceIdAuto (L : FlatLift t f) where
  /-- The underlying automorphism of the ambient scheme. -/
  hom : L.space ⟶ L.space
  /-- The automorphism is over `S'`. -/
  over : hom ≫ L.f' = L.f'
  /-- The automorphism reduces to the identity on `X`. -/
  restrict : L.i ≫ hom = L.i
  /-- The underlying morphism is an isomorphism. -/
  isIso : IsIso hom

namespace ReduceIdAuto

/-- Assemble a reducing-to-identity automorphism from an ambient automorphism over
`S'` fixing `X`. -/
def of {L : FlatLift t f} (hom : L.space ⟶ L.space)
    (over : hom ≫ L.f' = L.f') (restrict : L.i ≫ hom = L.i)
    [IsIso hom] : ReduceIdAuto L where
  hom := hom
  over := over
  restrict := restrict
  isIso := inferInstance

/-- The identity automorphism of a flat lift. -/
def id (L : FlatLift t f) : ReduceIdAuto L where
  hom := 𝟙 L.space
  over := Category.id_comp L.f'
  restrict := Category.comp_id L.i
  isIso := inferInstance

/-- A reducing-to-identity automorphism is over `S'`, fixes `X`, and is an
isomorphism. -/
theorem spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    φ.hom ≫ L.f' = L.f' ∧ L.i ≫ φ.hom = L.i ∧ IsIso φ.hom := ⟨φ.over, φ.restrict, φ.isIso⟩

/-- The underlying morphism of flat lifts associated to a reducing-to-identity automorphism. -/
def toHom {L : FlatLift t f} (φ : ReduceIdAuto L) : Hom L L where
  hom := φ.hom
  over := φ.over
  restrict := φ.restrict
  isIso := φ.isIso

end ReduceIdAuto

end FlatLift

end AlgebraicGeometry.Scheme.Thickening
