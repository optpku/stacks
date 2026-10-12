/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap99.Situation_99_5_1_Category

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
structure Obj (f : X ⟶ B) where
  /-- The test scheme over `B`. -/
  σ : CohStack.SchemesOver B
  /-- The invertible module on the fibre `X_T`. -/
  line : (CohStack.fiber f σ).Modules
  /-- The module is tensor-invertible. -/
  invertible : isInvertibleObject line

/-- Package an invertible module on a fibre as an object of `Obj f`. -/
def ofLine {f : X ⟶ B} (σ : CohStack.SchemesOver B)
    (L : (CohStack.fiber f σ).Modules) [isInvertibleObject L] : Obj f where
  σ := σ
  line := L
  invertible := inferInstance

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

/-- A morphism of Picard objects is a morphism of schemes over `B` together with
an isomorphism of the modules pulled back along the induced fibre map. -/
structure Hom {f : X ⟶ B} (x y : Obj f) where
  /-- The underlying morphism of schemes over `B`. -/
  base : x.σ ⟶ y.σ
  /-- The isomorphism `(h')^* y.line ≅ x.line` of modules on the fibre. -/
  iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line

/-- Build a Picard morphism from a morphism of schemes over `B` and a line
isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B} {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    Hom x y where
  base := base
  iso := iso

/-- The underlying morphism of schemes of `homMk` is the supplied base map. -/
theorem homMk_base {f : X ⟶ B} {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    (homMk base iso).base = base := sorry

/-- The module component of `homMk` is the supplied isomorphism. -/
theorem homMk_iso {f : X ⟶ B} {x y : Obj f} (base : x.σ ⟶ y.σ)
    (iso : (Modules.pullback (CohStack.fiberMap f base)).obj y.line ≅ x.line) :
    (homMk base iso).iso = iso := sorry

/-- The identity comparison `(fiberMap f (𝟙))^* x.line ≅ x.line`, obtained by
transporting `modulesPullbackId` along `fiberMapIdIso.hom`. -/
def Hom.idIso {f : X ⟶ B} (x : Obj f) :
    (Modules.pullback (CohStack.fiberMap f (𝟙 x.σ))).obj x.line ≅ x.line :=
  (CohStack.pullbackFiberMapIdIso f x.σ).app x.line ≪≫
    (SmallEtaleModuleGlueing.modulesPullbackId (CohStack.fiber f x.σ)).app x.line

/-- The identity morphism uses the identity scheme map over `B` and the
comparison isomorphism along `fiberMap f (𝟙)`. -/
def Hom.id {f : X ⟶ B} (x : Obj f) : Hom x x where
  base := 𝟙 x.σ
  iso := Hom.idIso x

/-- The module isomorphism of a composite morphism, conjugating by
`Modules.pullbackCompIso` along the fibre maps of the factors. -/
def Hom.compIso {f : X ⟶ B} {x y z : Obj f} (α : Hom x y) (β : Hom y z) :
    (Modules.pullback
        (CohStack.fiberMap f α.base ≫ CohStack.fiberMap f β.base)).obj z.line ≅
      x.line :=
  (Modules.pullbackCompIso (CohStack.fiberMap f α.base)
        (CohStack.fiberMap f β.base)).symm.app z.line ≪≫
    (Modules.pullback (CohStack.fiberMap f α.base)).mapIso β.iso ≪≫ α.iso

/-- Composition of morphisms is composition of scheme maps over `B` and of the
conjugated module isomorphisms along `fiberMap` of the composite. -/
def Hom.comp {f : X ⟶ B} {x y z : Obj f} (α : Hom x y) (β : Hom y z) : Hom x z where
  base := α.base ≫ β.base
  iso := (CohStack.pullbackFiberMapCompIso f α.base β.base).app z.line ≪≫
    Hom.compIso α β

/-- Triples `(T, g, L)` and iso-morphisms `(h, φ)` form a category. -/
instance category (f : X ⟶ B) : Category (Obj f) where
  Hom := Hom
  id := Hom.id
  comp := fun α β ↦ Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection `(T, g, L) ↦ T` from `Obj f` to `(Sch/S)`. -/
def p (f : X ⟶ B) : Obj f ⥤ Over S where
  obj x := x.σ.left
  map α := α.base.left
  map_id := sorry
  map_comp := sorry

/-- The object part of `p` is the underlying scheme over `S`. -/
theorem p_obj {f : X ⟶ B} (x : Obj f) : (p f).obj x = x.σ.left := sorry

/-- The morphism part of `p` is the underlying morphism of schemes over `S`. -/
theorem p_map {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    (p f).map α = α.base.left := sorry

/-- The Picard projection is fibered in groupoids over `Over S`. -/
instance p_isFiberedInGroupoids (f : X ⟶ B) :
    Functor.IsFibered.InGroupoids (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
