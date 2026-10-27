/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.NegativeExt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Equality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Identity

/-! # The category of relatively perfect complexes on fibres

Objects are schemes over the base equipped with relatively perfect complexes with vanishing
negative self-Ext on field-valued fibres. Morphisms are base maps with derived pullback isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An object of the category of complexes on `X/B`: a scheme over `B` together
with a relatively perfect complex on the fibre whose negative self-Ext groups
vanish on field-valued fibres. -/
structure Object (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] where
  /-- The test scheme over `B`. -/
  σ : SchemeOver B
  /-- The complex on the fibre `X_T`. -/
  complex : ModuleDerived (pullback f σ.hom)
  /-- The complex is `T`-perfect. -/
  isPerfectRelative :
    ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex
  /-- Negative self-Ext groups vanish on every field-valued fibre over `T`. -/
  fiberNegativeSelfExtVanish :
    ∀ t : FieldValuedPoint (ofOver σ.left),
      ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t

/-- Package a test scheme and an admissible complex on the fibre as an object of
`Object f`. -/
def Object.of {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f] (σ : SchemeOver B)
    (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    Object f where
  σ := σ
  complex := complex
  isPerfectRelative := isPerfectRelative
  fiberNegativeSelfExtVanish := fiberNegativeSelfExtVanish

/-- The test scheme of `Object.of σ complex hPerfect hVanish` is `σ`. -/
theorem Object.of_σ {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (σ : SchemeOver B) (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    (Object.of σ complex isPerfectRelative fiberNegativeSelfExtVanish).σ = σ := sorry

/-- The complex of `Object.of σ complex hPerfect hVanish` is `complex`. -/
theorem Object.of_complex {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (σ : SchemeOver B) (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    (Object.of σ complex isPerfectRelative fiberNegativeSelfExtVanish).complex = complex := sorry

/-- An object of `Object f` is a `T`-perfect complex on the fibre with fibrewise
negative self-Ext vanishing. -/
theorem Object.spec {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Object f) :
    ModuleDerived.IsPerfectRelativeTo (pullback.snd f x.σ.hom) x.complex ∧
      ∀ t : FieldValuedPoint (ofOver x.σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f x.σ.hom)
          x.complex x.complex t := sorry

set_option maxHeartbeats 800000 in
/-- A morphism `(T, g, E) ⟶ (T', g', E')` is a morphism of schemes over `B`
together with an isomorphism `L(h')^* y.complex ≅ x.complex` along the base
change of that morphism. -/
structure Hom {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (x y : Object f) : Type (u + 1) where
  /-- The underlying morphism of schemes over `B`. -/
  base : x.σ ⟶ y.σ
  /-- The isomorphism `L(h')^* y.complex ≅ x.complex` in `D(𝒪_{X_T})`. -/
  iso : CategoryTheory.Iso (C := ModuleDerived (pullback f x.σ.hom))
    ((ModuleDerived.pullback (CohStack.fiberMap f base)).obj y.complex) x.complex

/-- Build a morphism of `Object f` from a morphism of schemes over `B` and a
derived-category isomorphism along the induced fibre map. -/
def Hom.of {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f] {x y : Object f}
    (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (CohStack.fiberMap f base)).obj y.complex ≅ x.complex) :
    Hom x y where
  base := base
  iso := iso

/-- The underlying morphism of schemes of `Hom.of` is the supplied base map. -/
theorem Hom.of_base {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (CohStack.fiberMap f base)).obj y.complex ≅ x.complex) :
    (Hom.of base iso).base = base := sorry

/-- The derived-category component of `Hom.of` is the supplied isomorphism. -/
theorem Hom.of_iso {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (CohStack.fiberMap f base)).obj y.complex ≅ x.complex) :
    (Hom.of base iso).iso = iso := sorry

/-- A morphism constructed from a base map and an isomorphism has both supplied components. -/
theorem Hom.of_spec {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (CohStack.fiberMap f base)).obj y.complex ≅ x.complex) :
    (Hom.of base iso).base = base ∧ (Hom.of base iso).iso = iso := sorry

/-- The identity comparison `L(CohStack.fiberMap f (𝟙))^* x.complex ≅ x.complex`. -/
def Hom.idIso {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Object f) :
    (ModuleDerived.pullback (CohStack.fiberMap f (𝟙 x.σ))).obj x.complex ≅ x.complex :=
  (ModuleDerived.pullbackCongr (CohStack.fiberMap_id_eq f x.σ)).app x.complex ≪≫
    (ModuleDerived.pullbackId (pullback f x.σ.hom)).app x.complex

/-- The identity morphism uses the identity scheme map over `B` and the comparison
isomorphism along `CohStack.fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f] (x : Object f) :
    Hom x x where
  base := 𝟙 x.σ
  iso := Hom.idIso x

/-- The derived-category component of the identity morphism is `Hom.idIso`. -/
theorem Hom.id_iso {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Object f) :
    (Hom.id x).iso = Hom.idIso x := sorry

/-- The derived isomorphism of a composite morphism, conjugating by
`ModuleDerived.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y z : Object f}
    (α : Hom x y) (β : Hom y z) :
    (ModuleDerived.pullback (CohStack.fiberMap f α.base ≫ CohStack.fiberMap f β.base)).obj z.complex ≅
      x.complex :=
  (ModuleDerived.pullbackCompIso (CohStack.fiberMap f α.base) (CohStack.fiberMap f β.base)).symm.app
      z.complex ≪≫
    (ModuleDerived.pullback (CohStack.fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- Composition of morphisms is composition of scheme maps over `B` and of the
conjugated derived isomorphisms along `CohStack.fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y z : Object f}
    (α : Hom x y) (β : Hom y z) :
    Hom x z where
  base := α.base ≫ β.base
  iso := (ModuleDerived.pullbackCongr (CohStack.fiberMap_comp_eq f α.base β.base)).app z.complex ≪≫
    Hom.compIso α β

/-- Composing an identity on the left leaves a morphism unchanged. -/
theorem Hom.id_comp {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Object f} (α : Hom x y) : Hom.comp (Hom.id x) α = α := sorry

/-- Composing an identity on the right leaves a morphism unchanged. -/
theorem Hom.comp_id {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y : Object f} (α : Hom x y) : Hom.comp α (Hom.id y) = α := sorry

/-- Composition of base maps and derived pullback isomorphisms is associative. -/
theorem Hom.assoc {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {w x y z : Object f} (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The category of relatively perfect complexes on scheme-valued fibres with vanishing
negative fibre self-Ext, with derived pullback isomorphisms as morphisms. -/
def category (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    CategoryTheory.Cat.{u + 1, u + 1} :=
  ⟨Object f, {
    Hom := Hom
    id := Hom.id
    comp := fun α β ↦ Hom.comp α β
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

/-- Morphisms in `category f` are pairs consisting of a morphism of schemes over `B`
and an isomorphism of the complexes pulled back along the induced fibre map. -/
def homSigma {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    (x y : category f) :
    (x ⟶ y) ≃
      Σ (h : x.σ ⟶ y.σ),
        (ModuleDerived.pullback (CohStack.fiberMap f h)).obj y.complex ≅ x.complex where
  toFun := fun φ ↦ ⟨φ.base, φ.iso⟩
  invFun := fun pair ↦ Hom.of pair.1 pair.2
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Applying `homSigma` extracts the base morphism and derived isomorphism. -/
theorem homSigma_apply {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category f} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.base, φ.iso⟩ := sorry

/-- The inverse of `homSigma` reconstructs a morphism from a base map and a
derived isomorphism along the induced fibre map. -/
theorem homSigma_symm_apply {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category f}
    (pair : Σ (h : x.σ ⟶ y.σ),
      (ModuleDerived.pullback (CohStack.fiberMap f h)).obj y.complex ≅ x.complex) :
    (homSigma x y).symm pair = Hom.of pair.1 pair.2 := sorry

/-- The base map of an identity projects to the identity of the test scheme over `S`. -/
theorem pMapId {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    (x : category f) : (Hom.id x).base.left = 𝟙 x.σ.left := sorry

/-- The base map of a composite projects to the composite of the test-scheme maps. -/
theorem pMapComp {f : X ⟶ B} [Proper f] [Flat f] [FinitePresentation f]
    {x y z : category f} (α : x ⟶ y) (β : y ⟶ z) :
    (Hom.comp α β).base.left = α.base.left ≫ β.base.left := sorry

/-- The projection `(T, g, E) ↦ T` from `category f` to `(Sch/S)`. -/
def p (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] : category f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := pMapId
  map_comp := fun α β ↦ pMapComp α β

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f] (x : category f) :
    (p f).obj x = x.σ.left := sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B}
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category f}
    (α : x ⟶ y) :
    (p f).map α = α.base.left := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
