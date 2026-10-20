/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReasLib.CategoryTheory.Adjunction.Exactness
public import ReasLib.CategoryTheory.Monoidal.Duality.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Braided closed monoidal category API

This module provides source-order tensor/internal-Hom bridges in a braided monoidal closed
category. The constructions are independent of sheaves, rings, and any particular application.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe v u

namespace CategoryTheory.MonoidalClosed

/-- Currying in tensor order, obtained from the standard internal-Hom adjunction by transport
along the braiding. -/
@[stacks 03EO "Hom equivalence"]
def braidedHomEquiv {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalClosed A] (K L M : A) :
    (K ⊗ L ⟶ M) ≃ (K ⟶ (ihom L).obj M) :=
  ((β_ K L).homCongr (Iso.refl M)).trans
    (internalHomAdjunction₂.homEquiv :
      (L ⊗ K ⟶ M) ≃ (K ⟶ (ihom L).obj M))

/-- Currying in tensor order for an explicitly chosen closed monoidal structure, obtained by
transporting its internal-Hom adjunction along the braiding. -/
@[stacks 03EO "Hom equivalence from an explicit closed owner"]
noncomputable def braidedHomEquivOf
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    (H : MonoidalClosed A) (K L M : A) :
    (K ⊗ L ⟶ M) ≃
      (K ⟶ ((@MonoidalClosed.internalHom A _ _ H).obj (Opposite.op L)).obj M) :=
  ((β_ K L).homCongr (Iso.refl M)).trans
    ((@MonoidalClosed.internalHomAdjunction₂ A _ _ H).homEquiv :
      (L ⊗ K ⟶ M) ≃
        (K ⟶ ((@MonoidalClosed.internalHom A _ _ H).obj (Opposite.op L)).obj M))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of source-order currying is the braiding followed by uncurrying. -/
theorem braidedHomEquiv_symm_apply
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    {K L M : A} (f : K ⟶ (ihom L).obj M) :
    (braidedHomEquiv K L M).symm f = (β_ K L).hom ≫ uncurry f := by
  simp [braidedHomEquiv, uncurry, internalHomAdjunction₂,
    ParametrizedAdjunction.homEquiv_eq]
  change ((ihom.adjunction L).homEquiv K M).symm f =
    ((ihom.adjunction L).homEquiv K M).symm f
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of source-order currying selected by an explicit closed owner is the braiding
followed by the inverse of the selected tensor/internal-Hom adjunction equivalence. -/
theorem braidedHomEquivOf_symm_apply
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    (H : MonoidalClosed A) {K L M : A}
    (f : K ⟶ ((@MonoidalClosed.internalHom A _ _ H).obj (Opposite.op L)).obj M) :
    (braidedHomEquivOf H K L M).symm f =
      (β_ K L).hom ≫
        (((@MonoidalClosed.internalHomAdjunction₂ A _ _ H).adj L).homEquiv K M).symm f := by
  simp [braidedHomEquivOf, ParametrizedAdjunction.homEquiv_eq]
  change (((@MonoidalClosed.internalHomAdjunction₂ A _ _ H).adj L).homEquiv K M).symm f =
    (((@MonoidalClosed.internalHomAdjunction₂ A _ _ H).adj L).homEquiv K M).symm f
  rfl

/-- The tensor-left functor of `K ⊗ L` is canonically the composite of the tensor-left
functors of `K` and `L`, with source order preserved by the braiding. -/
abbrev tensorLeftTensorIso {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] (K L : A) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((tensoringLeft A).mapIso (β_ K L)) ≪≫ tensorLeftTensor L K

/-- The source-order adjunction between tensoring by `K ⊗ L` and the iterated internal-Hom
functor.  This is the functor-level owner behind `internalHomTensorIso`; it can be reused directly
for mates and adjunction transport without reconstructing a proof-local adjunction. -/
@[stacks 03EO "iterated internal-Hom adjunction"]
noncomputable def tensorLeftTensorAdjunction
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K L : A) : tensorLeft (K ⊗ L) ⊣ ihom L ⋙ ihom K :=
  (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
    (tensorLeftTensorIso K L).symm)

namespace InternalHomTensor

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  [MonoidalClosed A]

/-- Iterated internal Hom is naturally isomorphic to internal Hom out of a tensor product. -/
@[stacks 01CN, stacks 03EO, stacks 08DJ "functor-level internal Hom"]
noncomputable def natIso (K L : A) :
    ihom L ⋙ ihom K ≅ ihom (K ⊗ L) :=
  (Adjunction.rightAdjointUniq (ihom.adjunction (K ⊗ L))
    (tensorLeftTensorAdjunction K L)).symm

/-- The natural comparison from iterated internal Hom to internal Hom out of a tensor product. -/
@[stacks 03EO "iterated internal-Hom natural transformation"]
noncomputable def natTrans (K L : A) :
    ihom L ⋙ ihom K ⟶ ihom (K ⊗ L) :=
  (natIso K L).hom

/-- The inverse natural comparison from internal Hom out of a tensor product to iterated
internal Hom. -/
@[stacks 03EO "inverse iterated internal-Hom natural transformation"]
noncomputable def natTransInv (K L : A) :
    ihom (K ⊗ L) ⟶ ihom L ⋙ ihom K :=
  (natIso K L).inv

/-- Naturality of the iterated internal-Hom comparison in its target. -/
@[stacks 03EO "iterated internal-Hom naturality"]
theorem natTrans_naturality (K L : A) {M N : A} (f : M ⟶ N) :
    (ihom L ⋙ ihom K).map f ≫ (natTrans K L).app N =
      (natTrans K L).app M ≫ (ihom (K ⊗ L)).map f :=
  (natTrans K L).naturality f

/-- Naturality of the inverse iterated internal-Hom comparison in its target. -/
@[stacks 03EO "inverse iterated internal-Hom naturality"]
theorem natTransInv_naturality (K L : A) {M N : A} (f : M ⟶ N) :
    (ihom (K ⊗ L)).map f ≫ (natTransInv K L).app N =
      (natTransInv K L).app M ≫ (ihom L ⋙ ihom K).map f :=
  (natTransInv K L).naturality f

/-- The iterated internal-Hom comparison followed by its inverse is the identity. -/
@[simp, stacks 03EO "iterated internal-Hom forward-inverse law"]
theorem natTrans_hom_inv_id (K L : A) :
    natTrans K L ≫ natTransInv K L = 𝟙 _ :=
  (natIso K L).hom_inv_id

/-- The inverse iterated internal-Hom comparison followed by the comparison is the identity. -/
@[simp, stacks 03EO "iterated internal-Hom inverse-forward law"]
theorem natTrans_inv_hom_id (K L : A) :
    natTransInv K L ≫ natTrans K L = 𝟙 _ :=
  (natIso K L).inv_hom_id

/-- The forward and inverse comparison components compose to the identity. -/
@[simp, stacks 03EO "iterated internal-Hom component forward-inverse law"]
theorem natTrans_app_comp_inv_app (K L M : A) :
    (natTrans K L).app M ≫ (natTransInv K L).app M = 𝟙 _ :=
  (natIso K L).hom_inv_id_app M

/-- The inverse and forward comparison components compose to the identity. -/
@[simp, stacks 03EO "iterated internal-Hom component inverse-forward law"]
theorem natTransInv_app_comp_app (K L M : A) :
    (natTransInv K L).app M ≫ (natTrans K L).app M = 𝟙 _ :=
  (natIso K L).inv_hom_id_app M

/-- The forward natural transformation of the iterated internal-Hom isomorphism. -/
@[simp, stacks 03EO "iterated internal-Hom isomorphism hom"]
theorem natIso_hom (K L : A) :
    (natIso K L).hom = natTrans K L := rfl

/-- The inverse natural transformation of the iterated internal-Hom isomorphism. -/
@[simp, stacks 03EO "iterated internal-Hom isomorphism inverse"]
theorem natIso_inv (K L : A) :
    (natIso K L).inv = natTransInv K L := rfl

/-- The objectwise forward map of the iterated internal-Hom isomorphism. -/
@[simp, stacks 03EO "iterated internal-Hom isomorphism hom component"]
theorem natIso_hom_app (K L M : A) :
    (natIso K L).hom.app M = (natTrans K L).app M := rfl

/-- The objectwise inverse map of the iterated internal-Hom isomorphism. -/
@[simp, stacks 03EO "iterated internal-Hom isomorphism inverse component"]
theorem natIso_inv_app (K L M : A) :
    (natIso K L).inv.app M = (natTransInv K L).app M := rfl

end InternalHomTensor

/-- The currying isomorphism between an iterated internal Hom and the internal Hom out of a
tensor product in a braided closed monoidal category. -/
@[stacks 01CN, stacks 03EO, stacks 08DJ "internal Hom"]
noncomputable def internalHomTensorIso {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] [MonoidalClosed A] (K L M : A) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  (InternalHomTensor.natIso K L).app M

/-- The tensor/internal-Hom isomorphism is contravariantly natural in its first input. -/
theorem internalHomTensorIso_natural_left
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    {K K' L M : A} (f : K ⟶ K') :
    (pre f).app ((ihom L).obj M) ≫ (internalHomTensorIso K L M).hom =
      (internalHomTensorIso K' L M).hom ≫ (pre (f ▷ L)).app M := sorry

/-- The tensor/internal-Hom isomorphism is contravariantly natural in its second input. -/
theorem internalHomTensorIso_natural_middle
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K : A) {L L' M : A} (f : L ⟶ L') :
    (ihom K).map ((pre f).app M) ≫ (internalHomTensorIso K L M).hom =
      (internalHomTensorIso K L' M).hom ≫ (pre (K ◁ f)).app M := sorry

/-- The tensor/internal-Hom isomorphism is covariantly natural in its target. -/
theorem internalHomTensorIso_natural_right
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K L : A) {M M' : A} (f : M ⟶ M') :
    (ihom K).map ((ihom L).map f) ≫ (internalHomTensorIso K L M').hom =
      (internalHomTensorIso K L M).hom ≫ (ihom (K ⊗ L)).map f :=
  InternalHomTensor.natTrans_naturality K L f

/-- The canonical map from `K` to the internal Hom from `L` into `K ⊗ L`. -/
@[stacks 0A8W "tensor/internal-Hom unit"]
noncomputable def tensorInternalHomUnit {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] [MonoidalClosed A] (K L : A) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  curry (β_ L K).hom

/-- The tensor/internal-Hom unit is the coevaluation followed by the map induced by the
braiding. -/
theorem tensorInternalHomUnit_spec
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K L : A) :
    tensorInternalHomUnit K L =
      (ihom.coev L).app K ≫ (ihom L).map (β_ L K).hom :=
  curry_eq (β_ L K).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor/internal-Hom unit is natural in its left tensor factor. -/
theorem tensorInternalHomUnit_natural_left
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    {K₁ K₂ L : A} (f : K₁ ⟶ K₂) :
    CommSq f (tensorInternalHomUnit K₁ L) (tensorInternalHomUnit K₂ L)
      ((ihom L).map (f ▷ L)) := by
  exact ⟨by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_right]
    simp only [tensorInternalHomUnit, uncurry_curry]
    exact BraidedCategory.braiding_naturality_right L f⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor/internal-Hom unit is natural in its internal-Hom factor. -/
theorem tensorInternalHomUnit_natural_right
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K : A) {L₁ L₂ : A} (g : L₁ ⟶ L₂) :
    CommSq
      (tensorInternalHomUnit K L₂)
      (tensorInternalHomUnit K L₁)
      ((pre g).app (K ⊗ L₂))
      ((ihom L₁).map (K ◁ g)) := by
  exact ⟨by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_natural_right]
    simp only [tensorInternalHomUnit, uncurry_curry]
    exact BraidedCategory.braiding_naturality_left g K⟩

/-- The canonical comparison
`X ⊗ (X ⟶[A] 𝟙_ A) ⟶ (X ⟶[A] X)`.  It is enriched composition after identifying
`X` with the internal Hom from the tensor unit. -/
@[stacks 0FNY "tensor-to-endomorphism comparison"]
noncomputable def tensorIhomUnitToEnd
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) :
  X ⊗ (ihom X).obj (𝟙_ A) ⟶ (ihom X).obj X :=
  (β_ X ((ihom X).obj (𝟙_ A))).hom ≫
    ((ihom X).obj (𝟙_ A)) ◁ (unitIsoSelf (X := X)).inv ≫
    comp X (𝟙_ A) X

/-- The named inverse of the tensor-to-endomorphism comparison. -/
@[stacks 0FNY "tensor-to-endomorphism comparison inverse"]
noncomputable def tensorIhomUnitToEndInv
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    (ihom X).obj X ⟶ X ⊗ (ihom X).obj (𝟙_ A) :=
  CategoryTheory.inv (tensorIhomUnitToEnd X)

/-- The tensor-to-endomorphism comparison followed by its named inverse is the identity. -/
@[simp, stacks 0FNY "tensor-to-endomorphism comparison forward-inverse law"]
theorem tensorIhomUnitToEnd_hom_inv_id
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    tensorIhomUnitToEnd X ≫ tensorIhomUnitToEndInv X = 𝟙 _ :=
  IsIso.hom_inv_id _

/-- The named inverse followed by the tensor-to-endomorphism comparison is the identity. -/
@[simp, stacks 0FNY "tensor-to-endomorphism comparison inverse-forward law"]
theorem tensorIhomUnitToEnd_inv_hom_id
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    tensorIhomUnitToEndInv X ≫ tensorIhomUnitToEnd X = 𝟙 _ :=
  IsIso.inv_hom_id _

/-- The tensor-to-endomorphism comparison bundled with its named inverse. -/
@[stacks 0FNY "tensor-to-endomorphism comparison isomorphism"]
noncomputable def tensorIhomUnitToEndIso
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    X ⊗ (ihom X).obj (𝟙_ A) ≅ (ihom X).obj X where
  hom := tensorIhomUnitToEnd X
  inv := tensorIhomUnitToEndInv X
  hom_inv_id := tensorIhomUnitToEnd_hom_inv_id X
  inv_hom_id := tensorIhomUnitToEnd_inv_hom_id X

/-- The forward projection of the tensor-to-endomorphism comparison isomorphism. -/
@[simp, stacks 0FNY "tensor-to-endomorphism comparison isomorphism hom"]
theorem tensorIhomUnitToEndIso_hom
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    (tensorIhomUnitToEndIso X).hom = tensorIhomUnitToEnd X := rfl

/-- The inverse projection of the tensor-to-endomorphism comparison isomorphism. -/
@[simp, stacks 0FNY "tensor-to-endomorphism comparison isomorphism inverse"]
theorem tensorIhomUnitToEndIso_inv
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    (tensorIhomUnitToEndIso X).inv = tensorIhomUnitToEndInv X := rfl

/-- The coevaluation obtained by transporting the internal identity through the inverse of the
tensor-to-endomorphism comparison. -/
@[stacks 0FNY "canonical coevaluation"]
noncomputable def ihomUnitCoevaluation
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    𝟙_ A ⟶ (ihom X).obj (𝟙_ A) ⊗ X :=
  curry' (𝟙 X) ≫ tensorIhomUnitToEndInv X ≫
    (β_ X ((ihom X).obj (𝟙_ A))).hom

/-- The coevaluation transported from the internal identity and closed-structure evaluation
satisfy the triangle identity on the original object. -/
theorem ihomUnitCoevaluation_evaluation
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    X ◁ ihomUnitCoevaluation X ≫ (α_ X ((ihom X).obj (𝟙_ A)) X).inv ≫
        (ihom.ev X).app (𝟙_ A) ▷ X = (ρ_ X).hom ≫ (λ_ X).inv := sorry

/-- Closed-structure evaluation and the coevaluation transported from the internal identity
satisfy the triangle identity on the internal Hom into the tensor unit. -/
theorem ihomUnitEvaluation_coevaluation
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    ihomUnitCoevaluation X ▷ (ihom X).obj (𝟙_ A) ≫
        (α_ ((ihom X).obj (𝟙_ A)) X ((ihom X).obj (𝟙_ A))).hom ≫
        (ihom X).obj (𝟙_ A) ◁ (ihom.ev X).app (𝟙_ A) =
      (λ_ ((ihom X).obj (𝟙_ A))).hom ≫ (ρ_ ((ihom X).obj (𝟙_ A))).inv := sorry

/-- When the tensor-to-endomorphism comparison is invertible, the internal Hom into the tensor
unit is canonically a left dual. -/
@[stacks 0FNY "canonical left dual"]
noncomputable instance ihomUnitExactPairing
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    ExactPairing ((ihom X).obj (𝟙_ A)) X where
  coevaluation' := ihomUnitCoevaluation X
  evaluation' := (ihom.ev X).app (𝟙_ A)
  coevaluation_evaluation' := ihomUnitCoevaluation_evaluation X
  evaluation_coevaluation' := ihomUnitEvaluation_coevaluation X

/-- The coevaluation of the canonical internal-Hom exact pairing is the transported internal
identity. -/
@[simp]
theorem ihomUnitExactPairing_coevaluation
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    ExactPairing.coevaluation ((ihom X).obj (𝟙_ A)) X = ihomUnitCoevaluation X := rfl

/-- The evaluation of the canonical internal-Hom exact pairing is closed-structure
evaluation. -/
@[simp]
theorem ihomUnitExactPairing_evaluation
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (X : A) [IsIso (tensorIhomUnitToEnd X)] :
    ExactPairing.evaluation ((ihom X).obj (𝟙_ A)) X = (ihom.ev X).app (𝟙_ A) := rfl

/-- Right tensoring by a fixed object in a braided closed monoidal category is
right exact whenever finite colimits exist. -/
@[stacks 01CC]
theorem tensorRight_rightExact
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [Limits.HasFiniteColimits A] (K : A) [Closed K] :
    rightExactFunctor A A (tensorRight K) :=
  Adjunction.leftAdjoint_rightExact
    ((ihom.adjunction K).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight K))

end CategoryTheory.MonoidalClosed
