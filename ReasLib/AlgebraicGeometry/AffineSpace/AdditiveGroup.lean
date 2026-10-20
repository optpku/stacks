module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The additive group structure on affine space

Affine space over a scheme is a commutative group object under coordinatewise addition.
This module gives the structure maps explicitly and records their compatibility with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

namespace AlgebraicGeometry.AffineSpace

universe u

/-- The underlying scheme map of the zero section of affine space. -/
def zeroLeft (n : Type u) (S : Scheme.{u}) :
    (𝟙_ (Over S)).left ⟶ 𝔸(n; S) :=
  homOfVector (𝟙 S) (fun _ ↦ 0)

/-- The zero section of affine space is a morphism over the base scheme. -/
theorem zeroHom_w (n : Type u) (S : Scheme.{u}) :
    zeroLeft n S ≫ 𝔸(n; S) ↘ S = (𝟙_ (Over S)).hom := sorry

/-- The zero section of affine space as a morphism over the base scheme. -/
def zeroHom (n : Type u) (S : Scheme.{u}) :
    𝟙_ (Over S) ⟶ Scheme.asOver (𝔸(n; S)) S :=
  Over.homMk (zeroLeft n S) (zeroHom_w n S)

/-- The underlying scheme map which adds the coordinates of two points of affine space. -/
def addLeft (n : Type u) (S : Scheme.{u}) :
    (Scheme.asOver (𝔸(n; S)) S ⊗ Scheme.asOver (𝔸(n; S)) S).left ⟶ 𝔸(n; S) :=
  homOfVector (Scheme.asOver (𝔸(n; S)) S ⊗ Scheme.asOver (𝔸(n; S)) S).hom
    (fun i ↦
      (fst (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (coord S i) +
        (snd (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (coord S i))

/-- Coordinatewise addition on affine space is a morphism over the base scheme. -/
theorem addHom_w (n : Type u) (S : Scheme.{u}) :
    addLeft n S ≫ 𝔸(n; S) ↘ S =
      (Scheme.asOver (𝔸(n; S)) S ⊗ Scheme.asOver (𝔸(n; S)) S).hom := sorry

/-- Coordinatewise addition on affine space as a morphism over the base scheme. -/
def addHom (n : Type u) (S : Scheme.{u}) :
    Scheme.asOver (𝔸(n; S)) S ⊗ Scheme.asOver (𝔸(n; S)) S ⟶
      Scheme.asOver (𝔸(n; S)) S :=
  Over.homMk (addLeft n S) (addHom_w n S)

/-- The underlying scheme map which negates every coordinate of affine space. -/
def negLeft (n : Type u) (S : Scheme.{u}) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) (fun i ↦ -(coord S i))

/-- Coordinatewise negation on affine space is a morphism over the base scheme. -/
theorem negHom_w (n : Type u) (S : Scheme.{u}) :
    negLeft n S ≫ 𝔸(n; S) ↘ S = 𝔸(n; S) ↘ S := sorry

/-- Coordinatewise negation on affine space as a morphism over the base scheme. -/
def negHom (n : Type u) (S : Scheme.{u}) :
    Scheme.asOver (𝔸(n; S)) S ⟶ Scheme.asOver (𝔸(n; S)) S :=
  Over.homMk (negLeft n S) (negHom_w n S)

/-- Zero is a left identity for coordinatewise addition on affine space. -/
theorem zero_add (n : Type u) (S : Scheme.{u}) :
    zeroHom n S ▷ Scheme.asOver (𝔸(n; S)) S ≫ addHom n S =
      (λ_ (Scheme.asOver (𝔸(n; S)) S)).hom := sorry

/-- Zero is a right identity for coordinatewise addition on affine space. -/
theorem add_zero (n : Type u) (S : Scheme.{u}) :
    Scheme.asOver (𝔸(n; S)) S ◁ zeroHom n S ≫ addHom n S =
      (ρ_ (Scheme.asOver (𝔸(n; S)) S)).hom := sorry

/-- Coordinatewise addition on affine space is associative. -/
theorem add_assoc (n : Type u) (S : Scheme.{u}) :
    (addHom n S ▷ Scheme.asOver (𝔸(n; S)) S) ≫ addHom n S =
      (α_ _ _ _).hom ≫ (Scheme.asOver (𝔸(n; S)) S ◁ addHom n S) ≫ addHom n S := sorry

/-- Coordinatewise negation is a left inverse for addition on affine space. -/
theorem neg_add (n : Type u) (S : Scheme.{u}) :
    lift (negHom n S) (𝟙 (Scheme.asOver (𝔸(n; S)) S)) ≫ addHom n S =
      toUnit _ ≫ zeroHom n S := sorry

/-- Coordinatewise negation is a right inverse for addition on affine space. -/
theorem add_neg (n : Type u) (S : Scheme.{u}) :
    lift (𝟙 (Scheme.asOver (𝔸(n; S)) S)) (negHom n S) ≫ addHom n S =
      toUnit _ ≫ zeroHom n S := sorry

/-- Affine space over a scheme is canonically a group object under coordinatewise addition. -/
instance instGrpObjAsOver (n : Type u) (S : Scheme.{u}) :
    GrpObj (Scheme.asOver (𝔸(n; S)) S) where
  one := zeroHom n S
  mul := addHom n S
  one_mul := zero_add n S
  mul_one := add_zero n S
  mul_assoc := add_assoc n S
  inv := negHom n S
  left_inv := neg_add n S
  right_inv := add_neg n S

/-- Coordinatewise addition on affine space is commutative. -/
theorem add_comm (n : Type u) (S : Scheme.{u}) :
    (β_ (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).hom ≫ addHom n S =
      addHom n S := sorry

/-- Affine space is canonically a commutative monoid object under coordinatewise addition. -/
instance instIsCommMonObjAsOver (n : Type u) (S : Scheme.{u}) :
    IsCommMonObj (Scheme.asOver (𝔸(n; S)) S) where
  mul_comm := add_comm n S

/-- The pullback square for affine space gives the comparison over the new base. -/
def baseChangeSchemeIso (n : Type u) {S T : Scheme.{u}} (f : S ⟶ T) :
    Scheme.asOver (𝔸(n; S)) S ≅
      Scheme.asOver (pullback (𝔸(n; T) ↘ T) f) S :=
  Over.isoMk (isPullback_map (n := n) f).isoPullback
    (isPullback_map (n := n) f).isoPullback_hom_snd

/-- The affine-space base-change comparison preserves the group-object unit. -/
theorem baseChangeSchemeIso_hom_one (n : Type u) {S T : Scheme.{u}} (f : S ⟶ T) :
    η[Scheme.asOver (𝔸(n; S)) S] ≫ (baseChangeSchemeIso n f).hom =
      η[Scheme.asOver (pullback (𝔸(n; T) ↘ T) f) S] := sorry

/-- The affine-space base-change comparison preserves the group-object multiplication. -/
theorem baseChangeSchemeIso_hom_mul (n : Type u) {S T : Scheme.{u}} (f : S ⟶ T) :
    μ[Scheme.asOver (𝔸(n; S)) S] ≫ (baseChangeSchemeIso n f).hom =
      ((baseChangeSchemeIso n f).hom ⊗ₘ (baseChangeSchemeIso n f).hom) ≫
        μ[Scheme.asOver (pullback (𝔸(n; T) ↘ T) f) S] := sorry

/-- The affine-space base-change comparison preserves the coordinatewise monoid structure. -/
instance baseChangeSchemeIso_hom_isMonHom (n : Type u) {S T : Scheme.{u}} (f : S ⟶ T) :
    IsMonHom (baseChangeSchemeIso n f).hom where
  one_hom := baseChangeSchemeIso_hom_one n f
  mul_hom := baseChangeSchemeIso_hom_mul n f

/-- The coordinatewise commutative group on affine space agrees with its pullback. -/
def baseChangeCommGroupIso (n : Type u) {S T : Scheme.{u}} (f : S ⟶ T) :
    CommGrp.mk (Scheme.asOver (𝔸(n; S)) S) ≅
      (Over.pullback f).mapCommGrp.obj
        (CommGrp.mk (Scheme.asOver (𝔸(n; T)) T)) :=
  CommGrp.mkIso (baseChangeSchemeIso n f) (baseChangeSchemeIso_hom_one n f)
    (baseChangeSchemeIso_hom_mul n f)

/-- The unit of the affine-space group object pulls every coordinate back to zero. -/
theorem zero_appTop_coord (n : Type u) (S : Scheme.{u}) (i : n) :
    η[Scheme.asOver (𝔸(n; S)) S].left.appTop (coord S i) = 0 := sorry

/-- Addition on affine space pulls a coordinate back to the sum along the two projections. -/
theorem add_appTop_coord (n : Type u) (S : Scheme.{u}) (i : n) :
    μ[Scheme.asOver (𝔸(n; S)) S].left.appTop (coord S i) =
      (fst (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (coord S i) +
        (snd (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (coord S i) := sorry

/-- Inversion on affine space pulls every coordinate back to its negative. -/
theorem neg_appTop_coord (n : Type u) (S : Scheme.{u}) (i : n) :
    ι[Scheme.asOver (𝔸(n; S)) S].left.appTop (coord S i) = -(coord S i) := sorry

end AlgebraicGeometry.AffineSpace
