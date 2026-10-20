/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Proper

/-!
# The category of finitely presented flat modules with proper support on fibers

Objects consist of a test scheme over the target and a finitely presented module
on its fiber, flat over the test scheme and with proper support. Morphisms consist
of a base map together with an isomorphism from the pulled-back target module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Relative flatness of a module over the target of a morphism of algebraic spaces. -/
abbrev flatOver {Y Z : AlgebraicSpace S} (F : Y.Modules) (f : Y ⟶ Z) : Prop :=
  Modules.flatOver F f

/-- An object of the category of coherent sheaves on `X/B`: a scheme over `B`
together with a finitely presented module on the fibre, flat over the test
scheme, with support proper over the test scheme. -/
structure Object (f : X ⟶ B) [FinitePresentation f] where
  /-- The test scheme over `B`. -/
  σ : SchemesOver B
  /-- The module on the fibre `X_T`. -/
  module : (fiber f σ).Modules
  /-- The module is of finite presentation. -/
  isFinitePresentation : module.IsFinitePresentation
  /-- The module is flat over the test scheme. -/
  isFlat : Modules.flatOver module (fiberToBase f σ)
  /-- The support of the module is proper over the test scheme. -/
  hasProperSupport : Modules.HasProperSupportOver (fiberToBase f σ) module

/-- Package a test scheme and a finitely presented flat module with proper
support as an object of `Object f`. -/
def Object.of {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : Modules.flatOver module (fiberToBase f σ)) : Object f where
  σ := σ
  module := module
  isFinitePresentation := inferInstance
  isFlat := isFlat
  hasProperSupport := inferInstance

/-- A morphism `(T, g, F) ⟶ (T', g', F')` is a morphism of schemes over `B`
together with an isomorphism `(h')^* y.module ≅ x.module` along the base change
of that morphism. -/
def Hom {f : X ⟶ B} [FinitePresentation f] (x y : Object f) :=
  Σ (base : x.σ ⟶ y.σ), (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module

/-- The underlying morphism of schemes over `B` of a coherent-object morphism. -/
def Hom.base {f : X ⟶ B} [FinitePresentation f] {x y : Object f} (α : Hom x y) :
    x.σ ⟶ y.σ := α.1

/-- The module isomorphism along the fibre map of a coherent-object morphism. -/
def Hom.iso {f : X ⟶ B} [FinitePresentation f] {x y : Object f} (α : Hom x y) :
    (Modules.pullback (fiberMap f α.base)).obj y.module ≅ x.module := α.2

/-- Build a morphism of `Object f` from a morphism of schemes over `B` and a
module isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B} [FinitePresentation f] {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) : Hom x y :=
  ⟨base, iso⟩

/-- The underlying morphism of schemes of `homMk` is the supplied base map. -/
theorem homMk_base {f : X ⟶ B} [FinitePresentation f] {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) :
    (homMk base iso).base = base := sorry

/-- The module component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {f : X ⟶ B} [FinitePresentation f] {x y : Object f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) :
    (homMk base iso).iso = iso := sorry

/-- A morphism constructed from a base map and a module isomorphism has both supplied components. -/
theorem homMk_spec {f : X ⟶ B} [FinitePresentation f] {x y : Object f}
    (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (fiberMap f base)).obj y.module ≅ x.module) :
    (homMk base iso).base = base ∧ (homMk base iso).iso = iso := sorry

/-- Identification of module pullback along `fiberMap f (𝟙 σ)` with pullback along
the identity morphism of the fibre. -/
def pullbackFiberMapIdIso (f : X ⟶ B) (σ : SchemesOver B) :
    Modules.pullback (fiberMap f (𝟙 σ)) ≅ Modules.pullback (𝟙 (fiber f σ)) :=
  eqToIso (congrArg Modules.pullback (fiberMap_id_eq f σ))

/-- The identity comparison `(fiberMap f (𝟙))^* x.module ≅ x.module`, obtained by
transporting `Modules.pullbackIdIso` along `fiberMap_id_eq`. -/
def Hom.idIso {f : X ⟶ B} [FinitePresentation f] (x : Object f) :
    (Modules.pullback (fiberMap f (𝟙 x.σ))).obj x.module ≅ x.module :=
  (pullbackFiberMapIdIso f x.σ).app x.module ≪≫
    (Modules.pullbackIdIso (fiber f x.σ)).app x.module

/-- The identity morphism uses the identity scheme map over `B` and the comparison
isomorphism along `fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B} [FinitePresentation f] (x : Object f) : Hom x x :=
  homMk (𝟙 x.σ) (Hom.idIso x)

/-- The module isomorphism of a composite morphism, conjugating by
`Modules.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B} [FinitePresentation f] {x y z : Object f}
    (α : Hom x y) (β : Hom y z) :
    (Modules.pullback (fiberMap f α.base ≫ fiberMap f β.base)).obj z.module ≅ x.module :=
  (Modules.pullbackCompIso (fiberMap f α.base) (fiberMap f β.base)).symm.app z.module ≪≫
    (Modules.pullback (fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- Identification of module pullback along `fiberMap f (h ≫ k)` with pullback
along the composite of the individual fibre maps. -/
def pullbackFiberMapCompIso (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    Modules.pullback (fiberMap f (h ≫ k)) ≅
      Modules.pullback (fiberMap f h ≫ fiberMap f k) :=
  eqToIso (congrArg Modules.pullback (fiberMap_comp_eq f h k))

/-- Composition of morphisms is composition of scheme maps over `B` and of
the conjugated module isomorphisms along `fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B} [FinitePresentation f] {x y z : Object f}
    (α : Hom x y) (β : Hom y z) : Hom x z :=
  homMk (α.base ≫ β.base)
    ((pullbackFiberMapCompIso f α.base β.base).app z.module ≪≫ Hom.compIso α β)

/-- Composing the identity morphism on the left leaves a morphism unchanged. -/
theorem Hom.id_comp {f : X ⟶ B} [FinitePresentation f] {x y : Object f}
    (α : Hom x y) : Hom.comp (Hom.id x) α = α := sorry

/-- Composing the identity morphism on the right leaves a morphism unchanged. -/
theorem Hom.comp_id {f : X ⟶ B} [FinitePresentation f] {x y : Object f}
    (α : Hom x y) : Hom.comp α (Hom.id y) = α := sorry

/-- Composition of base maps and pullback isomorphisms is associative. -/
theorem Hom.assoc {f : X ⟶ B} [FinitePresentation f] {w x y z : Object f}
    (α : Hom w x) (β : Hom x y) (γ : Hom y z) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The category of finitely presented modules on scheme-valued fibers, flat over the test
scheme and with proper support, with pullback isomorphisms as morphisms. -/
def category (f : X ⟶ B) [FinitePresentation f] : CategoryTheory.Cat.{u + 1, u + 1} :=
  ⟨Object f, {
    Hom := Hom
    id := Hom.id
    comp := fun α β ↦ Hom.comp α β
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

/-- The carrier of the category of finitely presented flat modules with proper support on fibers. -/
abbrev Obj (f : X ⟶ B) [FinitePresentation f] : Type (u + 1) := category f

/-- Construct an object from a test scheme and a finitely presented flat module with proper support. -/
abbrev Obj.of {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) : Obj f :=
  Object.of σ module isFlat

/-- The test scheme of `Obj.of σ module isFlat` is `σ`. -/
theorem Obj.of_σ {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) :
    (Obj.of σ module isFlat).σ = σ := sorry

/-- The module of `Obj.of σ module isFlat` is `module`. -/
theorem Obj.of_module {f : X ⟶ B} [FinitePresentation f] (σ : SchemesOver B)
    (module : (fiber f σ).Modules) [module.IsFinitePresentation]
    [Modules.HasProperSupportOver (fiberToBase f σ) module]
    (isFlat : flatOver module (fiberToBase f σ)) :
    (Obj.of σ module isFlat).module = module := sorry

/-- An object of `Obj f` is a quasi-coherent finitely presented module on the
fibre, flat over the test scheme, with support proper over the test scheme. -/
theorem Obj.spec {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    x.module.IsQuasicoherent ∧ x.module.IsFinitePresentation ∧
      flatOver x.module (fiberToBase f x.σ) ∧
      Modules.HasProperSupportOver (fiberToBase f x.σ) x.module := sorry

/-- Morphisms in `Obj f` are pairs consisting of a morphism of schemes over `B`
and an isomorphism of the modules pulled back along the induced fibre map. -/
def homSigma {f : X ⟶ B} [FinitePresentation f] (x y : Obj f) :
    (x ⟶ y) ≃
      Σ (h : x.σ ⟶ y.σ),
        (Modules.pullback (fiberMap f h)).obj y.module ≅ x.module where
  toFun := fun φ ↦ ⟨φ.base, φ.iso⟩
  invFun := fun pair ↦ homMk pair.1 pair.2
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Applying `homSigma` extracts the base morphism and module isomorphism. -/
theorem homSigma_apply {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (φ : x ⟶ y) :
    homSigma x y φ = ⟨φ.base, φ.iso⟩ := sorry

/-- The inverse of `homSigma` reconstructs a morphism from a base map and a
module isomorphism along the induced fibre map. -/
theorem homSigma_symm_apply {f : X ⟶ B} [FinitePresentation f] {x y : Obj f}
    (pair : Σ (h : x.σ ⟶ y.σ),
      (Modules.pullback (fiberMap f h)).obj y.module ≅ x.module) :
    (homSigma x y).symm pair = homMk pair.1 pair.2 := sorry

/-- The base map of an identity morphism projects to an identity of schemes over `S`. -/
theorem pMapId {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (Hom.id x).base.left = 𝟙 x.σ.left := sorry

/-- The base map of a composite projects to the composite of the scheme maps over `S`. -/
theorem pMapComp {f : X ⟶ B} [FinitePresentation f] {x y z : Obj f}
    (α : x ⟶ y) (β : y ⟶ z) :
    (Hom.comp α β).base.left = α.base.left ≫ β.base.left := sorry

/-- The projection `(T, g, F) ↦ T` from `Obj f` to `(Sch/S)`. -/
def p (f : X ⟶ B) [FinitePresentation f] : Obj f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := pMapId
  map_comp := fun α β ↦ pMapComp α β

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (p f).obj x = x.σ.left := sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (p f).map α = α.base.left := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack

namespace AlgebraicGeometry.AlgebraicSpace

/-- The carrier of the category of finitely presented flat modules with proper support on fibers. -/
abbrev CohStack {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] := CohStack.Obj f

end AlgebraicGeometry.AlgebraicSpace
