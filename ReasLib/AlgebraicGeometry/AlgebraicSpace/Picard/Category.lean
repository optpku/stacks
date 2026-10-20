/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category

/-!
# Picard category of a morphism of algebraic spaces

Objects are triples `(T, g, L)` consisting of a scheme `T` over an algebraic
space `B` and an invertible module on the fibre `X_T`. Morphisms are pairs of
a morphism of schemes over `B` and an isomorphism of the pulled-back line
bundles along the induced fibre map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An object of the Picard category of `f : X ⟶ B`: a scheme over `B` together
with an invertible module on the fibre `X_T`. -/
structure Object (f : X ⟶ B) where
  /-- The test scheme over `B`. -/
  σ : CohStack.SchemesOver B
  /-- The invertible module on the fibre `X_T`. -/
  line : (CohStack.fiber f σ).Modules
  /-- The module is tensor-invertible. -/
  invertible : isInvertibleObject line

/-- Construct a Picard object from a test scheme and a tensor-invertible module. -/
def Object.ofLine {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] : Object f where
  σ := σ
  line := L
  invertible := inferInstance

/-- A morphism of Picard objects is a morphism of schemes over `B` together with
an isomorphism of the modules pulled back along the induced fibre map. -/
structure Hom {f : X ⟶ B} (x y : Object f) where
  /-- The underlying morphism of schemes over `B`. -/
  base : x.σ ⟶ y.σ
  /-- The isomorphism `(h')^* y.line ≅ x.line` of modules on the fibre. -/
  iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line

/-- Build a Picard morphism from a morphism of schemes over `B` and a line
isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B} {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    Hom x y where
  base := base
  iso := iso

/-- The underlying morphism of schemes of `homMk` is the supplied base map. -/
theorem homMk_base {f : X ⟶ B} {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    (homMk base iso).base = base := sorry

/-- The module component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {f : X ⟶ B} {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    (homMk base iso).iso = iso := sorry

/-- The identity comparison `(fiberMap f (𝟙))^* x.line ≅ x.line`, obtained by
transporting `Modules.pullbackIdIso` along the identity comparison. -/
def Hom.idIso {f : X ⟶ B} (x : Object f) :
    (Modules.pullback (CohStack.fiberMap f (𝟙 x.σ))).obj x.line ≅ x.line :=
  (CohStack.pullbackFiberMapIdIso f x.σ).app x.line ≪≫
    (Modules.pullbackIdIso (CohStack.fiber f x.σ)).app x.line

/-- The identity morphism uses the identity scheme map over `B` and the
comparison isomorphism along `fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B} (x : Object f) : Hom x x where
  base := 𝟙 x.σ
  iso := Hom.idIso x

/-- The module isomorphism of a composite morphism, conjugating by
`Modules.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B} {x y z : Object f} (α : Hom x y) (β : Hom y z) :
    (Modules.pullback (CohStack.fiberMap f α.base ≫ CohStack.fiberMap f β.base)).obj
      z.line ≅ x.line :=
  (Modules.pullbackCompIso (CohStack.fiberMap f α.base) (CohStack.fiberMap f β.base)).symm.app
    z.line ≪≫
    (Modules.pullback (CohStack.fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- Composition of morphisms is composition of scheme maps over `B` and of the
conjugated module isomorphisms along `fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B} {x y z : Object f} (α : Hom x y) (β : Hom y z) : Hom x z where
  base := α.base ≫ β.base
  iso := (CohStack.pullbackFiberMapCompIso f α.base β.base).app z.line ≪≫
    Hom.compIso α β

/-- Composing an identity on the left leaves a Picard morphism unchanged. -/
theorem Hom.id_comp {f : X ⟶ B} {x y : Object f} (α : Hom x y) :
    Hom.comp (Hom.id x) α = α := sorry

/-- Composing an identity on the right leaves a Picard morphism unchanged. -/
theorem Hom.comp_id {f : X ⟶ B} {x y : Object f} (α : Hom x y) :
    Hom.comp α (Hom.id y) = α := sorry

/-- Composition of Picard morphisms is associative. -/
theorem Hom.assoc {f : X ⟶ B} {w x y z : Object f}
    (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The category of invertible modules on scheme-valued fibers, with pullback
isomorphisms as morphisms. -/
def category (f : X ⟶ B) : CategoryTheory.Cat.{u + 1, u + 1} :=
  ⟨Object f, {
    Hom := Hom
    id := Hom.id
    comp := fun α β ↦ Hom.comp α β
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

/-- The carrier of the Picard category. -/
abbrev Obj (f : X ⟶ B) : Type (u + 1) := category f

/-- Construct an object of the Picard category from an invertible module. -/
def ofLine {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] : Obj f :=
  Object.ofLine σ L

/-- The test scheme of `ofLine σ L` is `σ`. -/
theorem ofLine_σ {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] :
    (ofLine σ L).σ = σ := sorry

/-- The module of `ofLine σ L` is `L`. -/
theorem ofLine_line {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] :
    (ofLine σ L).line = L := sorry

/-- An object of `Obj f` is an invertible module on the corresponding fibre. -/
theorem Obj.spec {f : X ⟶ B} (x : Obj f) : isInvertibleObject x.line := sorry

/-- An object constructed from an invertible module has the supplied test scheme
and module, and its module is tensor-invertible. -/
theorem ofLine_spec {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] :
    (ofLine σ L).σ = σ ∧ (ofLine σ L).line = L ∧
      isInvertibleObject (ofLine σ L).line := sorry

/-- A Picard morphism constructed from a base map and a module isomorphism has
both supplied components. -/
theorem homMk_spec {f : X ⟶ B} {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    (homMk base iso).base = base ∧ (homMk base iso).iso = iso := sorry

/-- The base map of an identity projects to the identity of the test scheme. -/
theorem pMapId {f : X ⟶ B} (x : Obj f) :
    (Hom.id x).base.left = 𝟙 x.σ.left := sorry

/-- The base map of a composite projects to the composite of the test scheme maps. -/
theorem pMapComp {f : X ⟶ B} {x y z : Obj f} (α : x ⟶ y) (β : y ⟶ z) :
    (Hom.comp α β).base.left = α.base.left ≫ β.base.left := sorry

/-- The projection `(T, g, L) ↦ T` from `Obj f` to `(Sch/S)`. -/
def p (f : X ⟶ B) : Obj f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := pMapId
  map_comp := fun α β ↦ pMapComp α β

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} (x : Obj f) : (p f).obj x = x.σ.left := sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    (p f).map α = α.base.left := sorry

/-- The Picard projection is fibered in groupoids over `Over S`. -/
instance p_isFiberedInGroupoids (f : X ⟶ B) :
    Functor.IsFibered.InGroupoids (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
