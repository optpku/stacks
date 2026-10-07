module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

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

/-- The commuting triangle used to lift a field-valued point of `X` into the fibre product
`Spec(K) ×_Z X`. -/
theorem fieldFiberPoint_w {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    𝟙 (ofOver p.overObj) ≫ (p.map g).hom = p.hom ≫ g :=
  sorry

/-- The fibre `X_z = Spec(K) ×_{z, Z} X` of `g : X ⟶ Z` at a field-valued point `p` of `X`. -/
noncomputable def fieldFiber {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    AlgebraicSpace S :=
  pullback (p.map g).hom g

/-- `fieldFiber p g` is the chosen fibre product of `p.map g` with `g`. -/
theorem fieldFiber_eq {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    fieldFiber p g = pullback (p.map g).hom g :=
  sorry
/-- The projection `X_z ⟶ X` of the field-valued fibre. -/
noncomputable def fieldFiberToSource {X Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (g : X ⟶ Z) : fieldFiber p g ⟶ X :=
  pullback.snd (p.map g).hom g

/-- `fieldFiberToSource p g` is the second projection of `fieldFiber p g`. -/
theorem fieldFiberToSource_eq {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    fieldFiberToSource p g = pullback.snd (p.map g).hom g :=
  sorry
/-- The identity-on-`Spec(K)` square for the induced map of field-valued fibres. -/
theorem fieldFiberHom_toZ {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    𝟙 (ofOver p.overObj) ≫ (p.map (f ≫ h)).hom =
      (p.map (f ≫ h)).hom ≫ 𝟙 Z :=
  sorry

/-- The `X ⟶ Y` square for the induced map of field-valued fibres. -/
theorem fieldFiberHom_toY {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    f ≫ h = (f ≫ h) ≫ 𝟙 Z :=
  sorry

/-- The fibre `Y_z = Spec(K) ×_{z, Z} Y` at the image of a field-valued point of `X`. -/
noncomputable def fieldFiberBase {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) : AlgebraicSpace S :=
  pullback (p.map (f ≫ h)).hom h

/-- `fieldFiberBase p f h` is the chosen fibre product of `p.map (f ≫ h)` with `h`. -/
theorem fieldFiberBase_eq {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    fieldFiberBase p f h = pullback (p.map (f ≫ h)).hom h :=
  sorry
/-- The induced morphism `X_z ⟶ Y_z` of field-valued fibres over `Z`. -/
noncomputable def fieldFiberHom {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    fieldFiber p (f ≫ h) ⟶ fieldFiberBase p f h :=
  pullback.map (p.map (f ≫ h)).hom (f ≫ h) (p.map (f ≫ h)).hom h
    (𝟙 (ofOver p.overObj)) f (𝟙 Z) (fieldFiberHom_toZ p f h) (fieldFiberHom_toY p f h)

/-- `fieldFiberHom p f h` is the `pullback.map` comparing the fibres of `f ≫ h` and `h`. -/
theorem fieldFiberHom_eq {X Y Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    fieldFiberHom p f h =
      pullback.map (p.map (f ≫ h)).hom (f ≫ h) (p.map (f ≫ h)).hom h
        (𝟙 (ofOver p.overObj)) f (𝟙 Z) (fieldFiberHom_toZ p f h) (fieldFiberHom_toY p f h) :=
  sorry
/-- The `K`-rational point of `X_z` determined by a field-valued point of `X`. -/
noncomputable def fieldFiberPoint {X Z : AlgebraicSpace S} (p : FieldValuedPoint X)
    (g : X ⟶ Z) : FieldValuedPoint (fieldFiber p g) :=
  FieldValuedPoint.of p.K p.structureHom
    (pullback.lift (𝟙 (ofOver p.overObj)) p.hom (fieldFiberPoint_w p g))

/-- The morphism of `fieldFiberPoint p g` is the universal lift of `p.hom` against `g`. -/
theorem fieldFiberPoint_hom {X Z : AlgebraicSpace S} (p : FieldValuedPoint X) (g : X ⟶ Z) :
    (fieldFiberPoint p g).hom =
      pullback.lift (𝟙 (ofOver p.overObj)) p.hom (fieldFiberPoint_w p g) :=
  sorry

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
  sorry
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
  sorry
/-- The extended fibre ideal of `Y` is contained in the comap of its extension to `X`. -/
theorem stalkFiberIdeal_le_comap (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    stalkFiberIdeal f h xbar ≤
      ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar)).comap
        (etaleLocalRingMap f xbar) :=
  sorry

/-- The quotient ring map
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ} →+* 𝒪_{X, x̄} / m_{z̄} 𝒪_{X, x̄}`. -/
noncomputable def stalkFiberRingHom (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    etaleLocalRing Y (xbar.map f) ⧸ stalkFiberIdeal f h xbar →+*
      etaleLocalRing X xbar ⧸ (stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar) :=
  Ideal.quotientMap ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar))
    (etaleLocalRingMap f xbar) (stalkFiberIdeal_le_comap f h xbar)

/-- `stalkFiberRingHom f h xbar` is `Ideal.quotientMap` along `etaleLocalRingMap f xbar`. -/
theorem stalkFiberRingHom_eq (f : X ⟶ Y) (h : Y ⟶ Z) (xbar : GeometricPoint X) :
    stalkFiberRingHom f h xbar =
      Ideal.quotientMap ((stalkFiberIdeal f h xbar).map (etaleLocalRingMap f xbar))
        (etaleLocalRingMap f xbar) (stalkFiberIdeal_le_comap f h xbar) :=
  sorry
/-- Condition (1) at a geometric point: `F_{x̄} / m_{z̄} F_{x̄}` is flat over
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ}`. -/
def stalkFiberFlatAlong (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) : Prop :=
  Module.FlatAlong (stalkFiberRingHom f h xbar) (stalkFiberModule F f h xbar)

/-- `stalkFiberFlatAlong` is flatness of the fibre stalk along `stalkFiberRingHom`. -/
theorem stalkFiberFlatAlong_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (xbar : GeometricPoint X) :
    stalkFiberFlatAlong F f h xbar ↔
      Module.FlatAlong (stalkFiberRingHom f h xbar) (stalkFiberModule F f h xbar) :=
  sorry

/-- Condition (2) at a field-valued point: the pullback of `F` to `X_z` is flat at the
`K`-rational point over `Y_z`. -/
def fieldFiberFlatOverAt (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (p : FieldValuedPoint X) : Prop :=
  flatOverAt ((pullback (fieldFiberToSource p (f ≫ h))).obj F)
    (fieldFiberHom p f h) (Points.mk (fieldFiberPoint p (f ≫ h)))

/-- `fieldFiberFlatOverAt` is `flatOverAt` of the pulled-back module on the field-valued
fibre. -/
theorem fieldFiberFlatOverAt_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z)
    (p : FieldValuedPoint X) :
    fieldFiberFlatOverAt F f h p ↔
      flatOverAt ((pullback (fieldFiberToSource p (f ≫ h))).obj F)
        (fieldFiberHom p f h) (Points.mk (fieldFiberPoint p (f ≫ h))) :=
  sorry

/-- Condition (3) at an étale scheme presentation: the pullback of `F` to the scheme fibre
`U_w` is flat over `V_w` at `u`. -/
def etaleFiberFlatOverAt (F : X.Modules) {U V W : Over S} (a : ofOver U ⟶ X)
    (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] (u : U.left) : Prop :=
  Scheme.Modules.flatOverAt
    ((Scheme.Modules.pullback
        ((toV.left ≫ toW.left).fiberι ((toV.left ≫ toW.left) u))).obj
      ((restrictToScheme (smallEtaleSite.mk a)).obj F))
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
          ((restrictToScheme (smallEtaleSite.mk a)).obj F))
        (Scheme.Hom.compFiberToBaseFiber toV.left toW.left ((toV.left ≫ toW.left) u))
        ((toV.left ≫ toW.left).asFiber u) :=
  sorry

/-- Condition (1): for every geometric point of `X` over `x`, the fibre stalk of `F` is flat
over the fibre of the étale local ring of `Y`. -/
def flatOnFiberAt_stalk (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x → stalkFiberFlatAlong F f h xbar

/-- `flatOnFiberAt_stalk` is the geometric-point fibre-stalk condition at every lift of `x`. -/
theorem flatOnFiberAt_stalk_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_stalk F f h x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → stalkFiberFlatAlong F f h xbar :=
  sorry

/-- Condition (2): for every field-valued representative of `x`, the pullback of `F` to the
fibre `X_z` is flat at `x` over `Y_z`. -/
def flatOnFiberAt_field (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → fieldFiberFlatOverAt F f h p

/-- `flatOnFiberAt_field` is the field-valued fibre-product condition at every representative
of `x`. -/
theorem flatOnFiberAt_field_iff (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    flatOnFiberAt_field F f h x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x → fieldFiberFlatOverAt F f h p :=
  sorry

/-- Condition (3): for every étale scheme presentation of the triangle through a germ over `x`,
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
  sorry

/-- Lemma 76.23.1: let `S` be a scheme and let `f : X ⟶ Y`, `h : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module and let `x ∈ |X|`. The
following are equivalent. (1) For a geometric point `xbar` of `X` over `x`, writing
`ȳ = xbar.map f` and `z̄ = ȳ.map h`, the module `F_{x̄} / m_{z̄} F_{x̄}` is flat over
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ}`. (2) For a morphism `Spec(K) ⟶ X` in the class of `x`, writing
`z` for its composite to `Z`, `X_z = Spec(K) ×_Z X`, `Y_z = Spec(K) ×_Z Y`, and `F_z` the
pullback of `F` to `X_z`, the sheaf `F_z` is flat at `x` over `Y_z`. (3) For schemes `U, V, W`
étale over `X, Y, Z` fitting in a commutative diagram, and a point `u ∈ U` mapping to `x` with
image `w ∈ W`, the pullback of `F` to the fibre `U_w` is flat over `V_w` at `u`. -/
@[stacks 05WY]
theorem flatOnFiberAt_tfae (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (h : Y ⟶ Z)
    (x : Points X) :
    List.TFAE [flatOnFiberAt_stalk F f h x, flatOnFiberAt_field F f h x,
      flatOnFiberAt_etale F f h x] :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
