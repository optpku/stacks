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
public import ReasLib.AlgebraicGeometry.ConstantGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap65.Lemma_65_14_3_Relation

/-!
# Affine profinite translation presentation

This module records the affine scheme `Y = Spec(LocallyConstant G k)` of an infinite
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

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] : base k = Spec (CommRingCat.of k) := sorry

/-- The coordinate ring of locally constant `k`-valued maps on a profinite group. -/
abbrev coordRing (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Type u :=
  LocallyConstant G k

/-- The coordinate ring is the ring of locally constant maps `G → k`. -/
theorem coordRing_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    coordRing k G = LocallyConstant G k := sorry

/-- The structure morphism of the coordinate ring as a `k`-algebra. -/
def algebraHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    CommRingCat.of k ⟶ CommRingCat.of (coordRing k G) :=
  CommRingCat.ofHom (algebraMap k (coordRing k G))

/-- `algebraHom` is `algebraMap` of the locally constant coordinate ring. -/
theorem algebraHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    algebraHom k G = CommRingCat.ofHom (algebraMap k (coordRing k G)) := sorry

/-- The affine scheme `Y = Spec(LocallyConstant G k)` over `Spec(k)`. -/
abbrev YOver (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Over (base k) :=
  OverSpec.affine (algebraHom k G)

/-- `YOver` is the affine object associated to `algebraHom`. -/
theorem YOver_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    YOver k G = OverSpec.affine (algebraHom k G) := sorry

/-- The underlying scheme of `YOver` is the spectrum of the coordinate ring. -/
theorem YOver_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (YOver k G).left = Spec (CommRingCat.of (coordRing k G)) := sorry

/-- The structure morphism of `YOver` is `Spec.map` of `algebraHom`. -/
theorem YOver_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (YOver k G).hom = Spec.map (algebraHom k G) := sorry

/-- The spectrum of the locally constant coordinate ring is affine. -/
instance instIsAffine_Y (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    AlgebraicGeometry.IsAffine (YOver k G).left := sorry

/-- Locally constant maps into a field form a reduced ring. -/
instance instIsReduced_coordRing (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    _root_.IsReduced (coordRing k G) := sorry

/-- The affine scheme `Y` is reduced. -/
instance instIsReduced_Y (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    AlgebraicGeometry.IsReduced (YOver k G).left := sorry

/-- The coordinate ring is zero-dimensional. -/
instance instKrullDimLE_zero_coordRing (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    Ring.KrullDimLE 0 (coordRing k G) := sorry

/-- Left multiplication by `g` as a continuous self-map of `G`. -/
def leftMul (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) : C(G, G) :=
  ContinuousMap.mulLeft g

/-- `leftMul` is left multiplication on the profinite group. -/
theorem leftMul_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    leftMul k G g = ContinuousMap.mulLeft g := sorry

/-- Precomposition of locally constant functions along left multiplication by `g`. -/
def translateRingHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    coordRing k G →+* coordRing k G :=
  LocallyConstant.comapRingHom (leftMul k G g)

/-- `translateRingHom` is `comap` along left multiplication. -/
theorem translateRingHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateRingHom k G g = LocallyConstant.comapRingHom (leftMul k G g) := sorry

/-- The scheme morphism of left translation by `g` on `Y`. -/
def translateLeft (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (YOver k G).left ⟶ (YOver k G).left :=
  Spec.map (CommRingCat.ofHom (translateRingHom k G g))

/-- `translateLeft` is `Spec.map` of precomposition along left multiplication. -/
theorem translateLeft_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateLeft k G g = Spec.map (CommRingCat.ofHom (translateRingHom k G g)) := sorry

/-- Left translation commutes with the structure morphism of `Y`. -/
theorem translate_w (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    translateLeft k G g ≫ (YOver k G).hom = (YOver k G).hom := sorry

/-- Left translation by `g` as a morphism of `Y` over `Spec(k)`. -/
def translate (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    YOver k G ⟶ YOver k G :=
  Over.homMk (translateLeft k G g) (translate_w k G g)

/-- The underlying scheme morphism of `translate` is `translateLeft`. -/
theorem translate_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translate k G g).left = translateLeft k G g := sorry

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
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `translateAut` is translation by `g`. -/
theorem translateAut_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translateAut k G g).hom = translate k G g := sorry

/-- The inverse map of `translateAut` is translation by `g⁻¹`. -/
theorem translateAut_inv (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    (translateAut k G g).inv = translate k G g⁻¹ := sorry

/-- The left translation action of `G` on `Y`. -/
def action (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : G →* Aut (YOver k G) where
  toFun g := translateAut k G g
  map_one' := sorry
  map_mul' := sorry

/-- The action of `g` is translation by `g`. -/
theorem action_apply (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    action k G g = translateAut k G g := sorry

/-- The defining arrow of `ofAut (action k G)` is the coproduct of graphs `(g · y, y)`. -/
theorem ofAut_action_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (ofAut (action k G)).hom = relationHom (action k G) := sorry

/-- The discrete coproduct `Γ = ∐_G Spec(k)` over `Spec(k)`. -/
def ΓOver (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Over (base k) :=
  ∐ fun _ : G ↦ Over.mk (𝟙 (base k))

/-- `ΓOver` is the coproduct of copies of `Spec(k)` indexed by `G`. -/
theorem ΓOver_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓOver k G = ∐ fun _ : G ↦ Over.mk (𝟙 (base k)) := sorry

/-- The structure morphism of `Γ` over `Spec(k)`, as a morphism of over-objects. -/
def ΓToBase (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓOver k G ⟶ Over.mk (𝟙 (base k)) :=
  Sigma.desc fun _ : G ↦ 𝟙 (Over.mk (𝟙 (base k)))

/-- `ΓToBase` is the coproduct fold of identities. -/
theorem ΓToBase_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓToBase k G = Sigma.desc fun _ : G ↦ 𝟙 (Over.mk (𝟙 (base k))) := sorry

/-- The `g`-component of the constant group scheme over `Spec(k)`. -/
def Γcomponent (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    Over.mk (𝟙 (base k)) ⟶ (ConstantGroup.baseChange (base k) (GrpCat.of G)).X :=
  (ConstantGroup.baseChangeHomEquiv (base k) (GrpCat.of G) (Over.mk (𝟙 (base k)))).symm
    (LocallyConstant.const (Over.mk (𝟙 (base k))).left g)

/-- `Γcomponent` is the point of the constant group scheme classified by the constant
value `g`. -/
theorem Γcomponent_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    Γcomponent k G g =
      (ConstantGroup.baseChangeHomEquiv (base k) (GrpCat.of G)
          (Over.mk (𝟙 (base k)))).symm
        (LocallyConstant.const (Over.mk (𝟙 (base k))).left g) := sorry

/-- Comparison from the discrete coproduct `Γ` to the constant group scheme over `Spec(k)`. -/
def ΓToConstantGroup (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓOver k G ⟶ (ConstantGroup.baseChange (base k) (GrpCat.of G)).X :=
  Sigma.desc fun g : G ↦ Γcomponent k G g

/-- `ΓToConstantGroup` is the coproduct fold of the constant-value components. -/
theorem ΓToConstantGroup_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    ΓToConstantGroup k G = Sigma.desc fun g : G ↦ Γcomponent k G g := sorry

/-- The comparison from the discrete coproduct to the constant group scheme is an
isomorphism. -/
instance instIsIso_ΓToConstantGroup (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    IsIso (ΓToConstantGroup k G) := sorry

/-- Evaluation of locally constant functions at the identity of `G`. -/
def originRingHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : coordRing k G →+* k :=
  LocallyConstant.evalRingHom (1 : G)

/-- `originRingHom` is evaluation at `1`. -/
theorem originRingHom_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originRingHom k G = LocallyConstant.evalRingHom (1 : G) := sorry

/-- The scheme morphism `Spec(k) ⟶ Y` associated to the origin of `G`. -/
def originLeft (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    base k ⟶ (YOver k G).left :=
  Spec.map (CommRingCat.ofHom (originRingHom k G))

/-- `originLeft` is `Spec.map` of evaluation at `1`. -/
theorem originLeft_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originLeft k G = Spec.map (CommRingCat.ofHom (originRingHom k G)) := sorry

/-- The origin morphism is a section of the structure morphism of `Y`. -/
theorem origin_w (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    originLeft k G ≫ (YOver k G).hom = 𝟙 (base k) := sorry

/-- The origin of `G` as a `k`-point of `Y` over `Spec(k)`. -/
def originHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    Over.mk (𝟙 (base k)) ⟶ YOver k G :=
  Over.homMk (originLeft k G) (origin_w k G)

/-- The underlying scheme morphism of `originHom` is `originLeft`. -/
theorem originHom_left (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (originHom k G).left = originLeft k G := sorry

/-- The orbit map `Γ ⟶ Y` sending the `g`-component to the translate of the origin by `g`. -/
def orbit (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : ΓOver k G ⟶ YOver k G :=
  Sigma.desc fun g : G ↦ originHom k G ≫ (action k G g).hom

/-- `orbit` is the coproduct fold of the translated origins. -/
theorem orbit_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    orbit k G = Sigma.desc fun g : G ↦ originHom k G ≫ (action k G g).hom := sorry

/-- On the `g`-summand, the orbit map is translation of the origin by `g`. -/
theorem orbit_ι (k : Type u) [Field k] (G : ProfiniteGrp.{u}) (g : G) :
    Sigma.ι (fun _ : G ↦ Over.mk (𝟙 (base k))) g ≫ orbit k G =
      originHom k G ≫ (action k G g).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
