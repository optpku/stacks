/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# Quasi-finite pushforward of coherent sheaves

Fibrewise direct image along a quasi-finite morphism of separated
finite-presentation algebraic spaces preserves coherent objects and commutes
with base change, defining a morphism of their groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.BasedCategory CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Pushforward of a coherent module on `X_T` along the fibre comparison `X_T ⟶ Y_T`. -/
def Obj.pushforward (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) : Obj y where
  σ := x.σ
  module := (Modules.pushforward (fiberComparison π y x.σ)).obj x.module
  isFinitePresentation := sorry
  isFlat := sorry
  hasProperSupport := sorry

/-- Objectwise pushforward preserves the underlying test scheme. -/
theorem Obj.pushforward_σ (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).σ = x.σ :=
  sorry

/-- Objectwise pushforward applies `π_{T,*}` to the module on the fibre. -/
theorem Obj.pushforward_module (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).module =
      (Modules.pushforward (fiberComparison π y x.σ)).obj x.module :=
  sorry

/-- The pushed module remains of finite presentation, flat over the test scheme,
and with proper support. -/
theorem Obj.pushforward_spec (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) :
    (Obj.pushforward π y x).module.IsFinitePresentation ∧
      flatOver (Obj.pushforward π y x).module (fiberToBase y x.σ) ∧
      Modules.HasProperSupportOver (fiberToBase y x.σ)
        (Obj.pushforward π y x).module :=
  sorry

/-- Forward base-change comparison
`(Y_{T'} → Y_T)^* π_{T,*} F ⟶ π_{T',*} (X_{T'} → X_T)^* F`. -/
def fiberPushforwardBaseChangeHom (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] {σ τ : SchemesOver B} (h : σ ⟶ τ)
    (F : (fiber (π ≫ y) τ).Modules) :
    (Modules.pullback (fiberMap y h)).obj
        ((Modules.pushforward (fiberComparison π y τ)).obj F) ⟶
      (Modules.pushforward (fiberComparison π y σ)).obj
        ((Modules.pullback (fiberMap (π ≫ y) h)).obj F) :=
  (Modules.baseChange (fiberComparison_isPullback π y h).w).app F

/-- The underived base-change comparison along the fibre square is an
isomorphism on the module of an object of `CohStack (π ≫ y)`. -/
theorem fiberPushforwardBaseChangeHom_isIso (π : X ⟶ Y) (y : Y ⟶ B)
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] (x : Obj (π ≫ y))
    {σ : SchemesOver B} (h : σ ⟶ x.σ) :
    IsIso (fiberPushforwardBaseChangeHom π y h x.module) :=
  sorry

/-- Base-change isomorphism on a `CohStack` object
`(Y_{T'} → Y_T)^* π_{T,*} F ≅ π_{T',*} (X_{T'} → X_T)^* F`. -/
def fiberPushforwardBaseChangeIso (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : Obj (π ≫ y)) {σ : SchemesOver B}
    (h : σ ⟶ x.σ) :
    (Modules.pullback (fiberMap y h)).obj
        ((Modules.pushforward (fiberComparison π y x.σ)).obj x.module) ≅
      (Modules.pushforward (fiberComparison π y σ)).obj
        ((Modules.pullback (fiberMap (π ≫ y) h)).obj x.module) :=
  @asIso _ _ _ _ (fiberPushforwardBaseChangeHom π y h x.module)
    (fiberPushforwardBaseChangeHom_isIso π y x h)

/-- The forward map of `fiberPushforwardBaseChangeIso` is the underived
base-change mate of the fibre comparison square at `x.module`. -/
theorem fiberPushforwardBaseChangeIso_hom (π : X ⟶ Y) (y : Y ⟶ B)
    [QuasiFinite π] [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] (x : Obj (π ≫ y))
    {σ : SchemesOver B} (h : σ ⟶ x.σ) :
    (fiberPushforwardBaseChangeIso π y x h).hom =
      fiberPushforwardBaseChangeHom π y h x.module :=
  sorry

/-- The morphism of `CohStack` objects induced by a fibrewise pushforward of
the module isomorphism along `π_{T,*}`. -/
def mapHom (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] {x x' : Obj (π ≫ y)} (α : Hom x x') :
    Hom (Obj.pushforward π y x) (Obj.pushforward π y x') :=
  homMk α.base
    (fiberPushforwardBaseChangeIso π y x' α.base ≪≫
      (Modules.pushforward (fiberComparison π y x.σ)).mapIso α.iso)

/-- The total functor of fibrewise quasi-finite pushforward
`CohStack (π ≫ y) ⥤ CohStack y`. -/
def mapFunctor (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    CohStack (π ≫ y) ⥤ CohStack y where
  obj := Obj.pushforward π y
  map α := mapHom π y α
  map_id := sorry
  map_comp := sorry

/-- `mapFunctor` lies strictly over `Over S`. -/
theorem mapFunctor_p (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    mapFunctor π y ⋙ p y = p (π ≫ y) :=
  sorry

/-- Objectwise, `mapFunctor` is `Obj.pushforward`. -/
theorem mapFunctor_obj (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    (mapFunctor π y).obj x = Obj.pushforward π y x :=
  sorry

/-- `mapFunctor` preserves the underlying test scheme. -/
theorem mapFunctor_obj_σ (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    ((mapFunctor π y).obj x).σ = x.σ :=
  sorry

/-- `mapFunctor` sends a module `F` on `X_T` to `π_{T,*} F` on `Y_T`. -/
theorem mapFunctor_obj_module (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] (x : CohStack (π ≫ y)) :
    ((mapFunctor π y).obj x).module =
      (Modules.pushforward (fiberComparison π y x.σ)).obj x.module :=
  sorry

/-- If `π : X ⟶ Y` is a quasi-finite morphism of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`, then
`π_*` induces a morphism of stacks `map π y : toGroupoids (π ≫ y) ⟶ toGroupoids y`
over `Over S`, sending `(T ⟶ B, F)` to `(T ⟶ B, π_{T,*} F)`. -/
def map (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    toGroupoids (π ≫ y) ⟶ toGroupoids y :=
  ofBasedFunctor (BasedFunctor.ofFunctor (mapFunctor π y) (mapFunctor_p π y))

/-- Forgetting `map` to based functors recovers `BasedFunctor.ofFunctor` of
`mapFunctor`. -/
theorem map.toBasedFunctor (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    FiberedCategoryOver.Groupoids.toBasedFunctor (map π y) =
      BasedFunctor.ofFunctor (mapFunctor π y) (mapFunctor_p π y) :=
  sorry

/-- The induced morphism of stacks lies strictly over `Over S`. -/
theorem map_p (π : X ⟶ Y) (y : Y ⟶ B) [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] :
    FiberedCategoryOver.Groupoids.toFunctor (map π y) ⋙ p y = p (π ≫ y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
