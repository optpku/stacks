/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Flat first-order lifts of morphisms of algebraic spaces

A flat lift of a flat morphism `f : X ⟶ Y` across a first-order thickening
`t : Y ⟶ Y'` of algebraic spaces over `S` is a pair `(f' : X' ⟶ Y', a : X ≅ X' ×_{Y'} Y)`
with `f'` flat and `a` over `Y`. The cartesian packaging is an `IsPullback` square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}

/-- The first-order conormal sheaf `𝒞_{Y/Y'}`, as `t^* (I/I²)` for the kernel
ideal sheaf of `t`. For a closed immersion this is the coborder formula of
`Hom.conormalSheaf t`. -/
abbrev thickeningConormal (t : Y ⟶ Y') [IsFirstOrderThickening t] : Y.Modules :=
  (Modules.pullback t).obj
    (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t))

/-- Inverse image of the first-order conormal sheaf of `t : Y ⟶ Y'` along
`f : X ⟶ Y`. This is `(f ≫ t)^* (I/I²)`, the composite form of `f^* 𝒞_{Y/Y'}`. -/
abbrev pulledConormal (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) :
    X.Modules :=
  (Modules.pullback (f ≫ t)).obj
    (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t))

/-- `pulledConormal t f` is the module pullback of `I/I²` along `f ≫ t`. -/
theorem pulledConormal_eq (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) :
    pulledConormal t f =
      (Modules.pullback (f ≫ t)).obj
        (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)) :=
  rfl

/-- First-order identification `I/I² ≅ I` of the kernel ideal of `t`, using
`I² = 0`. -/
def conormalToIdealIso (t : Y ⟶ Y') [IsFirstOrderThickening t] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t) ≅
      Hom.idealSheaf t :=
  cokernelIsoOfEq (IsFirstOrderThickening.square_zero (i := t)) ≪≫
    cokernelZeroIsoTarget

/-- First-order identification `I/I² ⟶ I` of the kernel ideal of `t`. -/
def conormalToIdeal (t : Y ⟶ Y') [IsFirstOrderThickening t] :
    Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t) ⟶
      Hom.idealSheaf t :=
  (conormalToIdealIso t).hom

/-- Canonical isomorphism `𝒞_{Y/Y'} ≅ t^* ℐ_{Y/Y'}` for a first-order
thickening. -/
def conormalIdealIso (t : Y ⟶ Y') [IsFirstOrderThickening t] :
    thickeningConormal t ≅ (Modules.pullback t).obj (Hom.idealSheaf t) :=
  (Modules.pullback t).mapIso (conormalToIdealIso t)

/-- `conormalIdealIso t` is the pullback of `conormalToIdealIso t`. -/
theorem conormalIdealIso_hom (t : Y ⟶ Y') [IsFirstOrderThickening t] :
    (conormalIdealIso t).hom = (Modules.pullback t).map (conormalToIdeal t) :=
  sorry

/-- The standard map `I/I² ⟶ (f ≫ t)_* ((f ≫ t)^* (I/I²))` of the first-order
deformation equation. -/
def canonicalKernelMap (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) :
    Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t) ⟶
      (Modules.pushforward (f ≫ t)).obj (pulledConormal t f) :=
  (Modules.pullbackPushforwardAdjunction (f ≫ t)).unit.app
    (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t))

/-- `canonicalKernelMap` is the adjunction unit of `(f ≫ t)^* ⊣ (f ≫ t)_*`. -/
theorem canonicalKernelMap_spec (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) :
    canonicalKernelMap t f =
      (Modules.pullbackPushforwardAdjunction (f ≫ t)).unit.app
        (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)) :=
  rfl

/-- Ext¹ of the naive cotangent complex of `f` against `f^* 𝒞_{Y/Y'}[0]` in
`D(𝒪_X-Mod)`. -/
abbrev extOneNL (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :=
  Ext⁽(1 : ℤ)⁾((DerivedCategory.Q).obj NL[f],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules X) 0).obj (pulledConormal t f)))

/-- Ext⁰ of the naive cotangent complex of `f` against `f^* 𝒞_{Y/Y'}[0]` in
`D(𝒪_X-Mod)`. -/
abbrev extZeroNL (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :=
  Ext⁽(0 : ℤ)⁾((DerivedCategory.Q).obj NL[f],
    (DerivedCategory.Q).obj
      ((CochainComplex.singleFunctor (Modules X) 0).obj (pulledConormal t f)))

/-- A flat first-order lift of `f : X ⟶ Y` across a first-order thickening
`t : Y ⟶ Y'`: a flat ambient morphism `f' : X' ⟶ Y'` whose closed fibre is
`Y`-isomorphic to `X`. -/
structure FlatLift (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] where
  /-- The ambient algebraic space `X'` of the lift. -/
  space : AlgebraicSpace S
  /-- The ambient morphism `f' : X' ⟶ Y'`. -/
  f' : space ⟶ Y'
  /-- The ambient morphism is flat. -/
  flat : Flat f'
  /-- The closed-fibre morphism `i : X ⟶ X'`. -/
  i : X ⟶ space
  /-- The square with `f`, `i`, `t`, `f'` is cartesian. -/
  isPullback : IsPullback f i t f'

namespace FlatLift

variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Assemble a flat lift from an ambient morphism, a closed-fibre morphism, and a
cartesian square. -/
def of {X' : AlgebraicSpace S} (f' : X' ⟶ Y') [Flat f'] (i : X ⟶ X')
    (isPullback : IsPullback f i t f') : FlatLift t f where
  space := X'
  f' := f'
  flat := inferInstance
  i := i
  isPullback := isPullback

/-- The commutative square of the closed-fibre pair `(f', a)` over `Y`. -/
theorem ofIso_commSq {X' : AlgebraicSpace S} (f' : X' ⟶ Y') [Flat f']
    (a : X ≅ pullback f' t) (over : a.hom ≫ pullback.snd f' t = f) :
    CommSq (a.hom ≫ pullback.fst f' t) f f' t := sorry

/-- The closed-fibre pair `(f', a)` over `Y` yields a cartesian square. -/
theorem ofIso_isPullback {X' : AlgebraicSpace S} (f' : X' ⟶ Y') [Flat f']
    (a : X ≅ pullback f' t) (over : a.hom ≫ pullback.snd f' t = f) :
    IsPullback f (a.hom ≫ pullback.fst f' t) t f' := sorry

/-- Recover a flat lift from a closed-fibre pair `(f' : X' ⟶ Y', a : X ≅ X' ×_{Y'} Y)`
over `Y`. -/
def ofIso {X' : AlgebraicSpace S} (f' : X' ⟶ Y') [Flat f']
    (a : X ≅ pullback f' t) (over : a.hom ≫ pullback.snd f' t = f) :
    FlatLift t f :=
  of f' (a.hom ≫ pullback.fst f' t) (ofIso_isPullback f' a over)

/-- The commutative square of a flat lift. -/
theorem sq (L : FlatLift t f) : CommSq f L.i t L.f' := sorry

/-- The closed-fibre isomorphism `a : X ≅ X' ×_{Y'} Y` of a flat lift. -/
def iso (L : FlatLift t f) : X ≅ pullback L.f' t :=
  L.isPullback.flip.isoPullback

/-- The isomorphism `L.iso` is over `Y`. -/
theorem iso_over (L : FlatLift t f) :
    L.iso.hom ≫ pullback.snd L.f' t = f := sorry

/-- A flat lift supplies a flat ambient morphism, a cartesian square, and a first-order
closed-fibre thickening. -/
theorem spec (L : FlatLift t f) :
    Flat L.f' ∧ IsPullback f L.i t L.f' ∧ IsFirstOrderThickening L.i := sorry

/-- The closed-fibre morphism of a flat lift is a first-order thickening. -/
theorem isFirstOrderThickening (L : FlatLift t f) :
    IsFirstOrderThickening L.i := sorry

/-- The closed-fibre coefficient sheaf of a cartesian lift, as
`(L.i ≫ L.f')^* (I_{Y/Y'} / I_{Y/Y'}²)`, canonically identified with
`C_{X/X'}` and with `f^* 𝒞_{Y/Y'}`. -/
abbrev liftConormal (L : FlatLift t f) : X.Modules :=
  (Modules.pullback (L.i ≫ L.f')).obj
    (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t))

/-- The closed-fibre ideal quotient `i^* (I_{X/X'} / I_{X/X'}²)`. -/
abbrev closedFibreConormal (L : FlatLift t f) : X.Modules :=
  (Modules.pullback L.i).obj
    (Modules.quotientByIdeal (Hom.idealSheafSubobject L.i) (Hom.idealSheaf L.i))

/-- Comparison `(L.i ≫ L.f')^* (I/I²) ≅ (f ≫ t)^* (I/I²)` of a cartesian lift,
via `L.isPullback.w`. -/
def liftConormalIso (L : FlatLift t f) : liftConormal L ≅ pulledConormal t f :=
  eqToIso
    (congrArg
      (fun g : X ⟶ Y' ↦
        (Modules.pullback g).obj
          (Modules.quotientByIdeal (Hom.idealSheafSubobject t) (Hom.idealSheaf t)))
      L.isPullback.w.symm)

/-- `liftConormalIso L` identifies the closed-fibre conormal with `f^* C_{Y/Y'}`. -/
theorem liftConormalIso_spec (L : FlatLift t f) :
    (liftConormalIso L).hom ≫ (liftConormalIso L).inv = 𝟙 (liftConormal L) ∧
      (liftConormalIso L).inv ≫ (liftConormalIso L).hom = 𝟙 (pulledConormal t f) :=
  sorry


/-- Morphisms of flat lifts: an isomorphism of ambient algebraic spaces over `Y'` reducing
to the identity on the closed fibre `X`. -/
structure Hom (L₁ L₂ : FlatLift t f) where
  /-- The underlying morphism of ambient algebraic spaces. -/
  hom : L₁.space ⟶ L₂.space
  /-- The morphism is over `Y'`. -/
  over : hom ≫ L₂.f' = L₁.f'
  /-- The morphism reduces to the identity on `X`. -/
  restrict : L₁.i ≫ hom = L₂.i
  /-- The underlying morphism is an isomorphism. -/
  isIso : IsIso hom

namespace Hom

/-- Assemble a morphism of flat lifts from an isomorphism of ambient algebraic spaces
compatible with `f'` and `i`. -/
def of {L₁ L₂ : FlatLift t f} (hom : L₁.space ⟶ L₂.space)
    (over : hom ≫ L₂.f' = L₁.f') (restrict : L₁.i ≫ hom = L₂.i)
    [IsIso hom] : Hom L₁ L₂ where
  hom := hom
  over := over
  restrict := restrict
  isIso := inferInstance

/-- A morphism of flat lifts is over `Y'`, reduces to `id` on `X`, and is an
isomorphism. -/
theorem spec {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    φ.hom ≫ L₂.f' = L₁.f' ∧ L₁.i ≫ φ.hom = L₂.i ∧ IsIso φ.hom := sorry

/-- The identity isomorphism of a flat lift. -/
def id (L : FlatLift t f) : Hom L L where
  hom := 𝟙 L.space
  over := Category.id_comp L.f'
  restrict := Category.comp_id L.i
  isIso := inferInstance

/-- Composition of isomorphisms over the thickened base fixing the closed fibre. -/
def comp {L₁ L₂ L₃ : FlatLift t f} (φ : Hom L₁ L₂) (ψ : Hom L₂ L₃) : Hom L₁ L₃ where
  hom := φ.hom ≫ ψ.hom
  over := (Category.assoc _ _ _).trans ((congrArg (φ.hom ≫ ·) ψ.over).trans φ.over)
  restrict := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ψ.hom) φ.restrict).trans ψ.restrict)
  isIso := ((@asIso _ _ _ _ φ.hom φ.isIso) ≪≫ (@asIso _ _ _ _ ψ.hom ψ.isIso)).isIso_hom

/-- The inverse of an isomorphism of flat lifts. -/
def symm {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) : Hom L₂ L₁ where
  hom := (@asIso _ _ _ _ φ.hom φ.isIso).inv
  over := by
    rw [← φ.over]
    exact (@asIso _ _ _ _ φ.hom φ.isIso).inv_hom_id_assoc _
  restrict := by
    rw [← φ.restrict, Category.assoc]
    exact (congrArg (L₁.i ≫ ·) (@asIso _ _ _ _ φ.hom φ.isIso).hom_inv_id).trans
      (Category.comp_id _)
  isIso := (@asIso _ _ _ _ φ.hom φ.isIso).isIso_inv

end Hom

/-- Automorphisms of a given flat lift over `Y'` which reduce to the identity on the
closed fibre `X ≅ X' ×_{Y'} Y`. -/
structure ReduceIdAuto (L : FlatLift t f) where
  /-- The underlying automorphism of the ambient algebraic space. -/
  hom : L.space ⟶ L.space
  /-- The automorphism is over `Y'`. -/
  over : hom ≫ L.f' = L.f'
  /-- The automorphism reduces to the identity on `X`. -/
  restrict : L.i ≫ hom = L.i
  /-- The underlying morphism is an isomorphism. -/
  isIso : IsIso hom

namespace ReduceIdAuto

/-- Assemble a reducing-to-identity automorphism from an ambient automorphism over
`Y'` fixing `X`. -/
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

/-- A reducing-to-identity automorphism is over `Y'`, fixes `X`, and is an
isomorphism. -/
theorem spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    φ.hom ≫ L.f' = L.f' ∧ L.i ≫ φ.hom = L.i ∧ IsIso φ.hom := sorry

/-- The underlying morphism of flat lifts associated to a reducing-to-identity
automorphism. -/
def toHom {L : FlatLift t f} (φ : ReduceIdAuto L) : Hom L L where
  hom := φ.hom
  over := φ.over
  restrict := φ.restrict
  isIso := φ.isIso

end ReduceIdAuto

end FlatLift

end AlgebraicGeometry.AlgebraicSpace.Thickening
