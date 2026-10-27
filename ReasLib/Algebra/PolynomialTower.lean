/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Polynomial squares over a tower of rings

Polynomial squares form a full subcategory of the slice of the arrow category.
Their two projections and tensor base change give polynomial algebras over the
three rings in the tower.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

-- Compatibility laws mention private tensor constructions without making those
-- constructions additional public operations.
set_option backward.privateInPublic true

namespace Algebra

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Polynomiality of the source and of the relative target of a square over `B → C`. -/
def isPolynomialTower : ObjectProperty
    (Over (Arrow.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C)))) :=
  fun X ↦ IsPolynomial A X.left.left ∧
    @IsPolynomial X.left.left X.left.right _ _ X.left.hom.hom.toRingHom.toAlgebra

/-- The category of commutative polynomial squares over the ring tower `A → B → C`. -/
abbrev PolynomialTower := (isPolynomialTower A B C).FullSubcategory

namespace PolynomialTower

variable {A B C}

/-- The first polynomial algebra in a polynomial square. -/
abbrev P (X : PolynomialTower A B C) : CommAlgCat A := X.obj.left.left

/-- The second algebra in a polynomial square, viewed over `A`. -/
abbrev Q (X : PolynomialTower A B C) : CommAlgCat A := X.obj.left.right

/-- The horizontal algebra map of a polynomial square. -/
abbrev toQ (X : PolynomialTower A B C) : P X ⟶ Q X := X.obj.left.hom

/-- The augmentation of the first polynomial algebra to `B`. -/
abbrev toB (X : PolynomialTower A B C) : P X ⟶ CommAlgCat.of A B := X.obj.hom.left

/-- The augmentation of the second polynomial algebra to `C`. -/
abbrev toC (X : PolynomialTower A B C) : Q X ⟶ CommAlgCat.of A C := X.obj.hom.right

/-- A polynomial square commutes with the fixed map `B → C`. -/
theorem square_commutes (X : PolynomialTower A B C) :
    toB X ≫ CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C) = toQ X ≫ toC X :=
  X.obj.hom.w

/-- A genuine commutative square of polynomial algebras defines a polynomial tower. -/
def ofSquare {P Q : CommAlgCat A} (pq : P ⟶ Q)
    (pb : P ⟶ CommAlgCat.of A B) (qc : Q ⟶ CommAlgCat.of A C)
    (w : pb ≫ CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C) = pq ≫ qc)
    (hp : IsPolynomial A P)
    (hq : @IsPolynomial P Q _ _ pq.hom.toRingHom.toAlgebra) : PolynomialTower A B C :=
  ⟨Over.mk (Arrow.homMk (f := Arrow.mk pq) pb qc w), hp, hq⟩

/-- The first projection of a morphism of polynomial squares. -/
abbrev mapP {X Y : PolynomialTower A B C} (f : X ⟶ Y) : P X ⟶ P Y :=
  f.hom.left.left

/-- The second projection of a morphism of polynomial squares. -/
abbrev mapQ {X Y : PolynomialTower A B C} (f : X ⟶ Y) : Q X ⟶ Q Y :=
  f.hom.left.right

/-- The first projection of a polynomial square is polynomial over `A`, with augmentation to `B`. -/
def base (X : PolynomialTower A B C) : PolynomialOver A B :=
  ⟨Over.mk (toB X), X.property.1⟩

variable (A B C) in
/-- Projection to the first polynomial algebra and its augmentation to `B`. -/
def forgetToBase : PolynomialTower A B C ⥤ PolynomialOver A B where
  obj := base
  map f := ObjectProperty.homMk (Over.homMk (mapP f)
    (congrArg (fun g ↦ g.left) f.hom.w))

/-- The second algebra of a polynomial square is polynomial over `A`. -/
theorem isPolynomial_overA (X : PolynomialTower A B C) : IsPolynomial A (Q X) := by
  letI : Algebra (P X) (Q X) := (toQ X).hom.toRingHom.toAlgebra
  letI : IsScalarTower A (P X) (Q X) := IsScalarTower.of_algHom (toQ X).hom
  obtain ⟨σ, ⟨eP⟩⟩ := X.property.1.exists_repr
  obtain ⟨τ, ⟨eQ⟩⟩ := X.property.2.exists_repr
  exact ⟨⟨τ ⊕ σ, ⟨((eQ.restrictScalars A).trans
    (MvPolynomial.mapAlgEquiv τ eP)).trans (MvPolynomial.sumAlgEquiv A τ σ).symm⟩⟩⟩

/-- The second projection of a polynomial square is polynomial over `A`, with augmentation to `C`. -/
def overA (X : PolynomialTower A B C) : PolynomialOver A C :=
  ⟨Over.mk (toC X), isPolynomial_overA X⟩

variable (A B C) in
/-- Projection to the second polynomial algebra, viewed as an `A`-algebra over `C`. -/
def forgetToOverA : PolynomialTower A B C ⥤ PolynomialOver A C where
  obj := overA
  map f := ObjectProperty.homMk (Over.homMk (mapQ f)
    (congrArg (fun g ↦ g.right) f.hom.w))

private def relativeQ (X : PolynomialTower A B C) : CommAlgCat (P X) :=
  @CommAlgCat.of (P X) _ (Q X) _ (toQ X).hom.toRingHom.toAlgebra

private def relativeB (X : PolynomialTower A B C) : CommAlgCat (P X) :=
  @CommAlgCat.of (P X) _ B _ (toB X).hom.toRingHom.toAlgebra

private def relativeC (X : PolynomialTower A B C) : CommAlgCat (P X) :=
  @CommAlgCat.of (P X) _ C _ ((toC X).hom.toRingHom.comp
    (toQ X).hom.toRingHom).toAlgebra

private def relativeToC (X : PolynomialTower A B C) :
    relativeQ X →ₐ[P X] relativeC X :=
  { (toC X).hom.toRingHom with commutes' := fun _ ↦ rfl }

/-- The map `B → C` respects the algebra structures induced by a polynomial square. -/
theorem toCOverP_commutes (X : PolynomialTower A B C) (p : P X) :
    algebraMap B C (toB X p) = toC X (toQ X p) := by
  exact congrArg (fun g : P X ⟶ CommAlgCat.of A C ↦ g p) (square_commutes X)

private def baseToC (X : PolynomialTower A B C) :
    relativeB X →ₐ[P X] relativeC X :=
  { (algebraMap B C : B →+* C) with commutes' := toCOverP_commutes X }

private def tensor (X : PolynomialTower A B C) : CommAlgCat B :=
  @CommAlgCat.of B _ (relativeQ X ⊗[P X] relativeB X) _
    (Algebra.TensorProduct.rightAlgebra (R := P X) (A := relativeQ X) (B := relativeB X))

private def tensorToCRingHom (X : PolynomialTower A B C) : tensor X →+* C :=
  (Algebra.TensorProduct.productMap (relativeToC X) (baseToC X)).toRingHom

/-- The tensor augmentation respects the canonical right `B`-algebra structure. -/
theorem tensorToC_commutes (X : PolynomialTower A B C) (b : B) :
    tensorToCRingHom X (algebraMap B (tensor X) b) = algebraMap B C b := by
  change toC X 1 * algebraMap B C b = algebraMap B C b
  simp

private def tensorToC (X : PolynomialTower A B C) : tensor X →ₐ[B] C :=
  { tensorToCRingHom X with commutes' := tensorToC_commutes X }

/-- Base change of the relative polynomial algebra is polynomial over `B`. -/
theorem isPolynomial_tensorOverBase (X : PolynomialTower A B C) :
    IsPolynomial B (tensor X) := by
  letI : Algebra (relativeB X) (relativeQ X ⊗[P X] relativeB X) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨σ, ⟨eQ⟩⟩ := X.property.2.exists_repr
  refine ⟨⟨σ, ?_⟩⟩
  change Nonempty ((relativeQ X ⊗[P X] relativeB X) ≃ₐ[relativeB X]
    MvPolynomial σ (relativeB X))
  exact ⟨((Algebra.TensorProduct.commRight (P X) (relativeB X)
    (relativeQ X)).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : relativeB X ≃ₐ[relativeB X] relativeB X) eQ)).trans
        (MvPolynomial.algebraTensorAlgEquiv (P X) (relativeB X))⟩

/-- The polynomial `B`-algebra obtained by tensoring the second ring with `B` over the first. -/
def tensorOverBase (X : PolynomialTower A B C) : PolynomialOver B C :=
  ⟨Over.mk (CommAlgCat.ofHom (tensorToC X)), isPolynomial_tensorOverBase X⟩

private def targetOverP (X Y : PolynomialTower A B C) : CommAlgCat (P X) :=
  @CommAlgCat.of (P X) _ (tensor Y) _
    ((algebraMap B (tensor Y)).comp (toB X).hom.toRingHom).toAlgebra

private def tensorLeftRingHom {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    Q X →+* tensor Y :=
  (Algebra.TensorProduct.includeLeftRingHom : relativeQ Y →+*
    relativeQ Y ⊗[P Y] relativeB Y).comp (mapQ f).hom.toRingHom

/-- The left factor of a map of tensor base changes respects the first source ring. -/
theorem tensorMapLeft_commutes {X Y : PolynomialTower A B C} (f : X ⟶ Y) (p : P X) :
    tensorLeftRingHom f (algebraMap (P X) (relativeQ X) p) =
      algebraMap (P X) (targetOverP X Y) p := by
  have hpq : mapQ f (toQ X p) = toQ Y (mapP f p) :=
    (congrArg (fun g : P X ⟶ Q Y ↦ g p) f.hom.left.w).symm
  have hpb : toB Y (mapP f p) = toB X p :=
    congrArg (fun g : P X ⟶ CommAlgCat.of A B ↦ g p)
      (congrArg (fun g ↦ g.left) f.hom.w)
  change (show relativeQ Y from mapQ f (toQ X p)) ⊗ₜ[P Y] (1 : relativeB Y) =
    (1 : relativeQ Y) ⊗ₜ[P Y] (show relativeB Y from toB X p)
  rw [hpq]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := P Y)
    (A := relativeQ Y) (B := relativeB Y) (mapP f p)).trans
      (congrArg (fun b : relativeB Y ↦ (1 : relativeQ Y) ⊗ₜ[P Y] b) hpb)

private def tensorMapLeft {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    relativeQ X →ₐ[P X] targetOverP X Y :=
  { tensorLeftRingHom f with commutes' := tensorMapLeft_commutes f }

/-- The right factor of a map of tensor base changes respects the first source ring. -/
theorem tensorMapRight_commutes {X Y : PolynomialTower A B C} (f : X ⟶ Y) (p : P X) :
    algebraMap B (tensor Y) (algebraMap (P X) (relativeB X) p) =
      algebraMap (P X) (targetOverP X Y) p := by
  rfl

private def tensorMapRight {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    relativeB X →ₐ[P X] targetOverP X Y :=
  { (algebraMap B (tensor Y) : B →+* tensor Y) with
    commutes' := tensorMapRight_commutes f }

private def tensorMapRingHom {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    tensor X →+* tensor Y :=
  (Algebra.TensorProduct.productMap (tensorMapLeft f) (tensorMapRight f)).toRingHom

private theorem tensorMapRingHom_tmul {X Y : PolynomialTower A B C} (f : X ⟶ Y)
    (q : relativeQ X) (b : relativeB X) :
    tensorMapRingHom f (q ⊗ₜ[P X] b) =
      (show relativeQ Y from mapQ f q) ⊗ₜ[P Y] (show relativeB Y from b) := by
  change ((show relativeQ Y from mapQ f q) ⊗ₜ[P Y] (1 : relativeB Y)) *
    ((1 : relativeQ Y) ⊗ₜ[P Y] (show relativeB Y from b)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- A map of tensor base changes is linear over the fixed base ring `B`. -/
theorem tensorMap_commutes {X Y : PolynomialTower A B C} (f : X ⟶ Y) (b : B) :
    tensorMapRingHom f (algebraMap B (tensor X) b) = algebraMap B (tensor Y) b := by
  change tensorMapRingHom f ((1 : relativeQ X) ⊗ₜ[P X] (show relativeB X from b)) = _
  rw [tensorMapRingHom_tmul]
  change (show relativeQ Y from mapQ f 1) ⊗ₜ[P Y] (show relativeB Y from b) = _
  rw [map_one]
  rfl

private def tensorMapAlg {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    tensor X →ₐ[B] tensor Y :=
  { tensorMapRingHom f with commutes' := tensorMap_commutes f }

/-- A map of tensor base changes commutes with the augmentations to `C`. -/
theorem tensorMap_w {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    CommAlgCat.ofHom (tensorMapAlg f) ≫ (tensorOverBase Y).obj.hom =
      (tensorOverBase X).obj.hom := by
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext
  · show _ = _
    apply RingHom.ext
    intro q
    change tensorToCRingHom Y (tensorMapRingHom f (q ⊗ₜ[P X] (1 : relativeB X))) =
      tensorToCRingHom X (q ⊗ₜ[P X] (1 : relativeB X))
    rw [tensorMapRingHom_tmul]
    change toC Y (mapQ f q) * algebraMap B C 1 = toC X q * algebraMap B C 1
    have hqc : toC Y (mapQ f q) = toC X q :=
      congrArg (fun g : Q X ⟶ CommAlgCat.of A C ↦ g q)
        (congrArg (fun g ↦ g.right) f.hom.w)
    rw [hqc]
  · show _ = _
    apply RingHom.ext
    intro b
    change tensorToCRingHom Y (tensorMapRingHom f ((1 : relativeQ X) ⊗ₜ[P X] b)) =
      tensorToCRingHom X ((1 : relativeQ X) ⊗ₜ[P X] b)
    rw [tensorMapRingHom_tmul]
    change toC Y (mapQ f 1) * algebraMap B C b = toC X 1 * algebraMap B C b
    simp

private def tensorMap {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    tensorOverBase X ⟶ tensorOverBase Y :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom (tensorMapAlg f)) (tensorMap_w f))

/-- Tensor base change sends identity maps of polynomial squares to identity maps. -/
theorem tensorMap_id (X : PolynomialTower A B C) :
    tensorMap (𝟙 X) = 𝟙 (tensorOverBase X) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext
  · show _ = _
    apply RingHom.ext
    intro q
    change tensorMapRingHom (𝟙 X) (q ⊗ₜ[P X] (1 : relativeB X)) = _
    rw [tensorMapRingHom_tmul]
    rfl
  · show _ = _
    apply RingHom.ext
    intro b
    change tensorMapRingHom (𝟙 X) ((1 : relativeQ X) ⊗ₜ[P X] b) = _
    rw [tensorMapRingHom_tmul]
    rfl

/-- Tensor base change preserves composition of maps of polynomial squares. -/
theorem tensorMap_comp {X Y Z : PolynomialTower A B C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorMap (f ≫ g) = tensorMap f ≫ tensorMap g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext
  · show _ = _
    apply RingHom.ext
    intro q
    change tensorMapRingHom (f ≫ g) (q ⊗ₜ[P X] (1 : relativeB X)) =
      tensorMapRingHom g (tensorMapRingHom f (q ⊗ₜ[P X] (1 : relativeB X)))
    rw [tensorMapRingHom_tmul, tensorMapRingHom_tmul, tensorMapRingHom_tmul]
    rfl
  · show _ = _
    apply RingHom.ext
    intro b
    change tensorMapRingHom (f ≫ g) ((1 : relativeQ X) ⊗ₜ[P X] b) =
      tensorMapRingHom g (tensorMapRingHom f ((1 : relativeQ X) ⊗ₜ[P X] b))
    rw [tensorMapRingHom_tmul, tensorMapRingHom_tmul, tensorMapRingHom_tmul]
    rfl

variable (A B C) in
/-- Tensor base change sends a polynomial square to its polynomial `B`-algebra over `C`. -/
def forgetToOverB : PolynomialTower A B C ⥤ PolynomialOver B C where
  obj := tensorOverBase
  map := tensorMap
  map_id := tensorMap_id
  map_comp := tensorMap_comp

/-- The first projection evaluates to the first augmented polynomial algebra. -/
theorem forgetToBase_obj (X : PolynomialTower A B C) :
    (forgetToBase A B C).obj X = base X := rfl

/-- The first projection sends a map of squares to its first component. -/
theorem forgetToBase_map {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    ((forgetToBase A B C).map f).hom.left = mapP f := rfl

/-- The second projection evaluates to the second augmented polynomial algebra. -/
theorem forgetToOverA_obj (X : PolynomialTower A B C) :
    (forgetToOverA A B C).obj X = overA X := rfl

/-- The second projection sends a map of squares to its second component. -/
theorem forgetToOverA_map {X Y : PolynomialTower A B C} (f : X ⟶ Y) :
    ((forgetToOverA A B C).map f).hom.left = mapQ f := rfl

/-- Tensor base change evaluates to the tensor augmentation. -/
theorem forgetToOverB_obj (X : PolynomialTower A B C) :
    (forgetToOverB A B C).obj X = tensorOverBase X := rfl

/-- The tensor of a map of squares sends a pure tensor to the tensor of its second component. -/
theorem forgetToOverB_map_tmul {X Y : PolynomialTower A B C} (f : X ⟶ Y)
    (q : relativeQ X) (b : relativeB X) :
    ((forgetToOverB A B C).map f).hom.left.hom (q ⊗ₜ[P X] b) =
      (show relativeQ Y from mapQ f q) ⊗ₜ[P Y] (show relativeB Y from b) := by
  change ((show relativeQ Y from mapQ f q) ⊗ₜ[P Y] (1 : relativeB Y)) *
    ((1 : relativeQ Y) ⊗ₜ[P Y] (show relativeB Y from b)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end PolynomialTower
end Algebra
