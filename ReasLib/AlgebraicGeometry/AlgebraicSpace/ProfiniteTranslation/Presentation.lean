/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.LocallyConstant.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction
public import ReasLib.Topology.LocallyConstant.Algebra

/-!
# Affine profinite translation presentation

This module records the affine scheme `Y = Spec(LocallyConstant G k)` of a
profinite group over a field, the discrete coproduct `Γ = ∐_G Spec(k)`, and the left
translation action used to present the quotient algebraic space `X = Y / Γ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

/-- The base scheme `Spec(k)`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- The coordinate ring of locally constant `k`-valued maps on a profinite group. -/
abbrev coordRing (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Type u :=
  LocallyConstant G k

/-- The structure morphism of the coordinate ring as a `k`-algebra. -/
def algebraHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    CommRingCat.of k ⟶ CommRingCat.of (coordRing k G) :=
  CommRingCat.ofHom (algebraMap k (coordRing k G))

/-- `algebraHom` is `algebraMap` of the locally constant coordinate ring. -/
theorem algebraHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    algebraHom k G = CommRingCat.ofHom (algebraMap k (coordRing k G)) := by rfl

/-- The affine scheme `Y = Spec(LocallyConstant G k)` over `Spec(k)`. -/
abbrev YOver (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Over (base k) :=
  OverSpec.affine (algebraHom k G)

/-- `YOver` is the affine object associated to `algebraHom`. -/
theorem YOver_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    YOver k G = OverSpec.affine (algebraHom k G) := by rfl

/-- The underlying scheme of `YOver` is the spectrum of the coordinate ring. -/
theorem YOver_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (YOver k G).left = Spec (CommRingCat.of (coordRing k G)) := by rfl

/-- The structure morphism of `YOver` is `Spec.map` of `algebraHom`. -/
theorem YOver_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (YOver k G).hom = Spec.map (algebraHom k G) := by rfl

/-- The affine scheme `Y` is reduced. -/
instance instIsReduced_Y (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    AlgebraicGeometry.IsReduced (YOver k G).left := by
  change AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (coordRing k G)))
  infer_instance

/-- Precomposition of locally constant functions along left multiplication by `g`. -/
def translateRingHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    coordRing k G →+* coordRing k G :=
  LocallyConstant.comapRingHom (ContinuousMap.mulLeft g)

/-- `translateRingHom` is `comap` along left multiplication. -/
theorem translateRingHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateRingHom k G g = LocallyConstant.comapRingHom (ContinuousMap.mulLeft g) := by rfl

/-- The scheme morphism of left translation by `g` on `Y`. -/
def translateLeft (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (YOver k G).left ⟶ (YOver k G).left :=
  Spec.map (CommRingCat.ofHom (translateRingHom k G g))

/-- `translateLeft` is `Spec.map` of precomposition along left multiplication. -/
theorem translateLeft_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateLeft k G g = Spec.map (CommRingCat.ofHom (translateRingHom k G g)) := by rfl

/-- Left translation commutes with the structure morphism of `Y`. -/
theorem translate_w (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateLeft k G g ≫ (YOver k G).hom = (YOver k G).hom := sorry

/-- Left translation by `g` as a morphism of `Y` over `Spec(k)`. -/
def translate (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    YOver k G ⟶ YOver k G :=
  Over.homMk (translateLeft k G g) (translate_w k G g)

/-- The underlying scheme morphism of `translate` is `translateLeft`. -/
theorem translate_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translate k G g).left = translateLeft k G g := by rfl

/-- Translation by the identity is the identity morphism. -/
theorem translate_one (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    translate k G 1 = 𝟙 (YOver k G) := sorry

/-- Left translation by `g * h` is translation by `h` followed by translation by `g`. -/
theorem translate_mul (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g h : G) :
    translate k G (g * h) = translate k G h ≫ translate k G g := sorry

/-- Translation by `g` is inverted by translation by `g⁻¹`. -/
theorem translate_inv (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translate k G g ≫ translate k G g⁻¹ = 𝟙 (YOver k G) := sorry

/-- Translation by `g⁻¹` is inverted by translation by `g`. -/
theorem translate_inv' (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translate k G g⁻¹ ≫ translate k G g = 𝟙 (YOver k G) := sorry

/-- Left translation by `g` as an automorphism of `Y` over `Spec(k)`. -/
def translateAut (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) : Aut (YOver k G) where
  hom := translate k G g
  inv := translate k G g⁻¹
  hom_inv_id := translate_inv k G g
  inv_hom_id := translate_inv' k G g

/-- The forward map of `translateAut` is translation by `g`. -/
theorem translateAut_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translateAut k G g).hom = translate k G g := by rfl

/-- The inverse map of `translateAut` is translation by `g⁻¹`. -/
theorem translateAut_inv (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translateAut k G g).inv = translate k G g⁻¹ := by rfl

/-- The left translation action of `G` on `Y`. -/
def action (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : G →* Aut (YOver k G) where
  toFun g := translateAut k G g
  map_one' := by
    apply Iso.ext
    exact translate_one k G
  map_mul' g h := by
    apply Iso.ext
    exact translate_mul k G g h

/-- The action of `g` is translation by `g`. -/
theorem action_apply (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    action k G g = translateAut k G g := by rfl

/-- The translation action on the spectrum of locally constant functions is residue-field free. -/
instance instIsResidueFieldFree_action (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    IsResidueFieldFree (action k G) := sorry

/-- The discrete coproduct `Γ = ∐_G Spec(k)` over `Spec(k)`. -/
def ΓOver (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Over (base k) :=
  ∐ fun _ : G ↦ Over.mk (𝟙 (base k))

/-- `ΓOver` is the coproduct of copies of `Spec(k)` indexed by `G`. -/
theorem ΓOver_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓOver k G = ∐ fun _ : G ↦ Over.mk (𝟙 (base k)) := by rfl

/-- The structure morphism of `Γ` over `Spec(k)`, as a morphism of over-objects. -/
def ΓToBase (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓOver k G ⟶ Over.mk (𝟙 (base k)) :=
  Sigma.desc fun _ : G ↦ 𝟙 (Over.mk (𝟙 (base k)))

/-- `ΓToBase` is the coproduct fold of identities. -/
theorem ΓToBase_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓToBase k G = Sigma.desc fun _ : G ↦ 𝟙 (Over.mk (𝟙 (base k))) := by rfl

/-- Evaluation of locally constant functions at the identity of `G`. -/
def originRingHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : coordRing k G →+* k :=
  LocallyConstant.evalRingHom (1 : G)

/-- `originRingHom` is evaluation at `1`. -/
theorem originRingHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originRingHom k G = LocallyConstant.evalRingHom (1 : G) := by rfl

/-- The scheme morphism `Spec(k) ⟶ Y` associated to the origin of `G`. -/
def originLeft (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    base k ⟶ (YOver k G).left :=
  Spec.map (CommRingCat.ofHom (originRingHom k G))

/-- `originLeft` is `Spec.map` of evaluation at `1`. -/
theorem originLeft_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originLeft k G = Spec.map (CommRingCat.ofHom (originRingHom k G)) := by rfl

/-- The origin morphism is a section of the structure morphism of `Y`. -/
theorem origin_w (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originLeft k G ≫ (YOver k G).hom = 𝟙 (base k) := sorry

/-- The origin of `G` as a `k`-point of `Y` over `Spec(k)`. -/
def originHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    Over.mk (𝟙 (base k)) ⟶ YOver k G :=
  Over.homMk (originLeft k G) (origin_w k G)

/-- The underlying scheme morphism of `originHom` is `originLeft`. -/
theorem originHom_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (originHom k G).left = originLeft k G := by rfl

/-- The orbit map `Γ ⟶ Y` sending the `g`-component to the translate of the origin by `g`. -/
def orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : ΓOver k G ⟶ YOver k G :=
  Sigma.desc fun g : G ↦ originHom k G ≫ (action k G g).hom

/-- `orbit` is the coproduct fold of the translated origins. -/
theorem orbit_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    orbit k G = Sigma.desc fun g : G ↦ originHom k G ≫ (action k G g).hom := by rfl

/-- On the `g`-summand, the orbit map is translation of the origin by `g`. -/
theorem orbit_ι (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    Sigma.ι (fun _ : G ↦ Over.mk (𝟙 (base k))) g ≫ orbit k G =
      originHom k G ≫ (action k G g).hom := by
  exact Sigma.ι_desc _ _

end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
