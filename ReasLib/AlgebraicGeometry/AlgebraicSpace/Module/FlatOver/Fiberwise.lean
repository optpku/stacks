/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition

/-!
# Fibrewise relative flatness at a point of an algebraic space

In a commutative triangle of algebraic spaces, relative flatness of a quasi-coherent module
along the fibre of `X ⟶ Z` over the fibre of `Y ⟶ Z` at a point of `|X|` may be tested on
étale stalks, on the field-valued fibre product, or on an étale scheme presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.Limits IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Modules

variable {X Y Z : AlgebraicSpace S}

/-- The ideal `m_{z̄} 𝒪_{Y, ȳ}` in the étale local ring of `Y` at `ȳ = xbar.map f`. -/
noncomputable def stalkFiberIdeal (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    Ideal (etaleLocalRing Y (xbar.map f)) :=
  (maximalIdeal (etaleLocalRing Z ((xbar.map f).map h))).map
    (etaleLocalRingMap h (xbar.map f))

/-- `stalkFiberIdeal f h xbar` is the extension of the maximal ideal of `𝒪_{Z, z̄}`. -/
theorem stalkFiberIdeal_eq (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    stalkFiberIdeal f h xbar =
      (maximalIdeal (etaleLocalRing Z ((xbar.map f).map h))).map
        (etaleLocalRingMap h (xbar.map f)) :=
  rfl
/-- The quotient module `F_{x̄} / m_{z̄} F_{x̄}` of the étale stalk along the fibre over `Z`. -/
noncomputable abbrev stalkFiberModule (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) :=
  stalkModuleCat xbar F ⧸
    ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar) •
      (⊤ : Submodule (etaleLocalRing X xbar) (stalkModuleCat xbar F)))

/-- `stalkFiberModule F f h xbar` is the quotient of the étale stalk by the extended maximal
ideal of `𝒪_{Z, z̄}`. -/
theorem stalkFiberModule_eq (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) :
    stalkFiberModule F f h xbar =
      (stalkModuleCat xbar F ⧸
        ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar) •
          (⊤ : Submodule (etaleLocalRing X xbar) (stalkModuleCat xbar F)))) :=
  rfl
/-- The quotient ring map
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ} →+* 𝒪_{X, x̄} / m_{z̄} 𝒪_{X, x̄}`. -/
noncomputable def stalkFiberRingHom (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    etaleLocalRing Y (xbar.map f) ⧸ stalkFiberIdeal f h xbar →+*
      etaleLocalRing X xbar ⧸ (stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar) :=
  Ideal.quotientMap ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar))
    (etaleLocalRingMap f xbar) (Ideal.le_comap_map)

/-- `stalkFiberRingHom f h xbar` is `Ideal.quotientMap` along `etaleLocalRingMap f xbar`. -/
theorem stalkFiberRingHom_eq (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    stalkFiberRingHom f h xbar =
      Ideal.quotientMap ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar))
        (etaleLocalRingMap f xbar) (Ideal.le_comap_map) :=
  rfl
/-- At a geometric point, `F_{x̄} / m_{z̄} F_{x̄}` is flat over
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ}`. -/
def stalkFiberFlatAlong (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) : Prop :=
  Module.FlatAlong (stalkFiberRingHom f h xbar) (stalkFiberModule F f h xbar)

/-- `stalkFiberFlatAlong` is flatness of the fibre stalk along `stalkFiberRingHom`. -/
theorem stalkFiberFlatAlong_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) :
    stalkFiberFlatAlong F f h xbar ↔
      Module.FlatAlong (stalkFiberRingHom f h xbar) (stalkFiberModule F f h xbar) :=
  Iff.rfl

/-- At a field-valued point, the pullback of `F` to `X_z` is flat at the
`K`-rational point over `Y_z`. -/
def fieldFiberFlatOverAt (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (p : FieldValuedPoint X) : Prop :=
  flatOverAt ((pullback (fieldFiberι (f ≫ h) (p.map (f ≫ h)))).obj F)
    (overBaseChange f h (p.map (f ≫ h)).hom) (Points.mk (fieldFiberPoint p (f ≫ h)))

/-- `fieldFiberFlatOverAt` is `flatOverAt` of the pulled-back module on the field-valued
fibre. -/
theorem fieldFiberFlatOverAt_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (p : FieldValuedPoint X) :
    fieldFiberFlatOverAt F f h p ↔
      flatOverAt ((pullback (fieldFiberι (f ≫ h) (p.map (f ≫ h)))).obj F)
        (overBaseChange f h (p.map (f ≫ h)).hom) (Points.mk (fieldFiberPoint p (f ≫ h))) :=
  Iff.rfl

/-- At an étale scheme presentation, the pullback of `F` to the scheme fibre
`U_w` is flat over `V_w` at `u`. -/
def etaleFiberFlatOverAt (F : X.Modules) {U V W : Over S} (a : ofOver U ⟶ X)
    (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] (u : U.left) : Prop :=
  Scheme.Modules.flatOverAt
    ((Scheme.Modules.pullback
        ((toV.left ≫ toW.left).fiberι ((toV.left ≫ toW.left) u))).obj
      ((restrictFunctor a ⋙ restrictToScheme U).obj F))
    (Scheme.Hom.compFiberToBaseFiber toV.left toW.left ((toV.left ≫ toW.left) u))
    ((toV.left ≫ toW.left).asFiber u)

/-- `etaleFiberFlatOverAt` is scheme-level `flatOverAt` on the fibre of `U ⟶ W` at the image
of `u`. -/
theorem etaleFiberFlatOverAt_iff (F : X.Modules) {U V W : Over S} (a : ofOver U ⟶ X)
    (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] (u : U.left) :
    etaleFiberFlatOverAt F a toV toW u ↔
      Scheme.Modules.flatOverAt
        ((Scheme.Modules.pullback
            ((toV.left ≫ toW.left).fiberι ((toV.left ≫ toW.left) u))).obj
          ((restrictFunctor a ⋙ restrictToScheme U).obj F))
        (Scheme.Hom.compFiberToBaseFiber toV.left toW.left ((toV.left ≫ toW.left) u))
        ((toV.left ≫ toW.left).asFiber u) :=
  Iff.rfl

/-- For every geometric point of `X` over `x`, the fibre stalk of `F` is flat
over the fibre of the étale local ring of `Y`. -/
def flatOnFiberAt_stalk (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x → stalkFiberFlatAlong F f h xbar

/-- `flatOnFiberAt_stalk` is the geometric-point fibre-stalk condition at every lift of `x`. -/
theorem flatOnFiberAt_stalk_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_stalk F f h x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → stalkFiberFlatAlong F f h xbar :=
  Iff.rfl

/-- For every field-valued representative of `x`, the pullback of `F` to the
fibre `X_z` is flat at `x` over `Y_z`. -/
def flatOnFiberAt_field (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → fieldFiberFlatOverAt F f h p

/-- `flatOnFiberAt_field` is the field-valued fibre-product condition at every representative
of `x`. -/
theorem flatOnFiberAt_field_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_field F f h x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x → fieldFiberFlatOverAt F f h p :=
  Iff.rfl

/-- For every étale scheme presentation of the triangle through a germ over `x`,
the restricted module is relatively flat on the scheme fibres. -/
def flatOnFiberAt_etale (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  ∀ (U V W : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (c : ofOver W ⟶ Z)
    (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] [Etale b] [Etale c] (u : U.left),
    a ≫ f = ofOverMap toV ≫ b →
      b ≫ h = ofOverMap toW ≫ c →
        Points.map a (ofOver.pointsEquiv U u) = x →
          etaleFiberFlatOverAt F a toV toW u

/-- `flatOnFiberAt_etale` is the étale-presentation fibre condition at every germ over `x`. -/
theorem flatOnFiberAt_etale_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_etale F f h x ↔
      ∀ (U V W : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (c : ofOver W ⟶ Z)
        (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] [Etale b] [Etale c] (u : U.left),
        a ≫ f = ofOverMap toV ≫ b →
          b ≫ h = ofOverMap toW ≫ c →
            Points.map a (ofOver.pointsEquiv U u) = x →
              etaleFiberFlatOverAt F a toV toW u :=
  Iff.rfl

/-- For any chosen geometric point, field-valued representative, and compatible étale
scheme presentation above the same point, the three fibrewise relative flatness tests for a
quasi-coherent module are equivalent. -/
theorem flatOnFiberAt_tfae (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (h : Y ⟶ Z)
    (x : Points X) (xbar : GeometricPoint X) (hxbar : xbar.liesOver x)
    (p : FieldValuedPoint X) (hp : Points.mk p = x)
    (U V W : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (c : ofOver W ⟶ Z)
    (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] [Etale b] [Etale c] (u : U.left)
    (hab : a ≫ f = ofOverMap toV ≫ b) (hbc : b ≫ h = ofOverMap toW ≫ c)
    (hu : Points.map a (ofOver.pointsEquiv U u) = x) :
    List.TFAE [stalkFiberFlatAlong F f h xbar, fieldFiberFlatOverAt F f h p,
      etaleFiberFlatOverAt F a toV toW u] :=
  sorry

/-- The universal geometric-stalk, field-valued fibre, and étale scheme-fibre tests for
relative flatness of a quasi-coherent module at a point are equivalent. -/
theorem flatOnFiberAt_forall_tfae (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (h : Y ⟶ Z)
    (x : Points X) :
    List.TFAE [flatOnFiberAt_stalk F f h x, flatOnFiberAt_field F f h x,
      flatOnFiberAt_etale F f h x] :=
  sorry

/-- For a quasi-coherent module, the field-valued fibre condition at `x` is equivalent to
the geometric-point fibre-stalk condition. -/
theorem flatOnFiberAt_field_iff_stalk (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y)
    (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_field F f h x ↔ flatOnFiberAt_stalk F f h x :=
  sorry

/-- For a quasi-coherent module, the field-valued fibre condition at `x` is equivalent to
the étale scheme-presentation condition. -/
theorem flatOnFiberAt_field_iff_etale (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y)
    (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_field F f h x ↔ flatOnFiberAt_etale F f h x :=
  sorry

end Modules

variable {X Y Z : AlgebraicSpace S}

/-- The fibre of `X` over the image of `x` in `|Z|` is flat at `x` over the fibre of `Y`. -/
def fiberFlatAt (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  Modules.flatOnFiberAt_field (SheafOfModules.unit (structureSheaf X)) f h x

/-- `fiberFlatAt` is fibrewise relative flatness of `𝒪_X`. -/
theorem fiberFlatAt_iff (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    fiberFlatAt f h x ↔
      Modules.flatOnFiberAt_field (SheafOfModules.unit (structureSheaf X)) f h x :=
  Iff.rfl

/-- The fibre of `X` over `z` is flat over the fibre of `Y` over `z`. -/
def fiberFlatOver (f : X ⟶ Y) (h : Y ⟶ Z) (z : Points Z) : Prop :=
  ∀ x : Points X, Points.map (f ≫ h) x = z → fiberFlatAt f h x

/-- `fiberFlatOver` is fibrewise relative flatness of `𝒪_X` at every point of `|X|` over
`z`. -/
theorem fiberFlatOver_iff (f : X ⟶ Y) (h : Y ⟶ Z) (z : Points Z) :
    fiberFlatOver f h z ↔
      ∀ x : Points X, Points.map (f ≫ h) x = z → fiberFlatAt f h x :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
