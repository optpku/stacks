/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.Pairing
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct

/-!
# Tensor characters of differential graded modules

This file realizes the middle term in the tensor-character adjunction.  The coefficient
`ℚ/ℤ` is the cochain complex concentrated in degree zero, so maps into it are literal morphisms
in `CochainComplex (ModuleCat ℤ) ℤ`.  The resulting equivalences separate the universal property
of the relative tensor product from the character-dual model.
-/

@[expose] public section

noncomputable section

universe s v w x

open CategoryTheory
open ComplexShape

namespace DifferentialGradedModule.TensorCharacter

variable {A : CochainDGAlgebra.{0, x} ℤ}

/-- The character group `ℚ/ℤ`, regarded as a `ℤ`-module in the universe of a tensor complex. -/
abbrev coefficient : ModuleCat.{s} ℤ :=
  (ModuleCat.uliftFunctor.{s, 0} ℤ).obj
    (ModuleCat.of ℤ (AddCircle (1 : ℚ)))

/-- The coefficient complex `ℚ/ℤ[0]` representing characters of cochain complexes. -/
@[stacks 09K3 "character coefficient complex"]
abbrev complex : CochainComplex (ModuleCat.{s} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{s} ℤ) (up ℤ) 0).obj coefficient

/-- Complementary homogeneous degrees sum to zero. -/
theorem complementaryDegree (p : ℤ) : p + -p = 0 := by omega

/-- Recover the complementary degree from a total-degree-zero decomposition. -/
theorem rightDegree {p q : ℤ} (h : p + q = 0) : q = -p := by omega

private theorem intLinear_of_add
    {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    (hX : Module ℤ X) (hY : Module ℤ Y) (f : X → Y)
    (hf : ∀ a b, f (a + b) = f a + f b) (r : ℤ) (x : X) :
    f (hX.smul r x) = hY.smul r (f x) := by
  rw [int_smul_eq_zsmul hX, int_smul_eq_zsmul hY]
  exact (AddMonoidHom.mk' f hf).map_zsmul r x

/-- A balanced pairing evaluated on one homogeneous tensor summand of total degree zero. -/
def pairingComponent
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) (p q : ℤ) (h : p + q = 0) :
    TensorProduct.baseTensor (R := ℤ) (N.X p) (M.X q) ⟶
      coefficient.{max v w} :=
  ModuleCat.TensorProduct.liftOfBilinear ℤ
    (fun x y ↦ ULift.up <| b.eval p x <|
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type w)) (rightDegree h)) y)
    (by
      intro x₁ x₂ y
      have hq : q = -p := by omega
      subst q
      letI : Module ℤ (CharacterModule (M.X (-p))) := CharacterModule.instModule ℤ _
      apply ULift.ext
      change ((b.hom p) (x₁ + x₂)) y = ((b.hom p) x₁) y + ((b.hom p) x₂) y
      exact congrArg (fun c : CharacterModule (M.X (-p)) ↦ c y)
        ((b.hom p).map_add x₁ x₂))
    (by
      intro r x y
      have hq : q = -p := by omega
      subst q
      refine @intLinear_of_add (N.X p) _ _ _ (N.X p).isModule
        ((ModuleCat.uliftFunctor.{max v w, 0} ℤ).obj
          (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).isModule
        (fun z ↦ ULift.up <| b.eval p z y) ?_ r x
      intro x₁ x₂
      letI : Module ℤ (CharacterModule (M.X (-p))) := CharacterModule.instModule ℤ _
      dsimp [BalancedPairing.eval]
      rw [(b.hom p).map_add]
      rfl)
    (by
      intro x y₁ y₂
      have hq : q = -p := by omega
      subst q
      apply ULift.ext
      exact (b.hom p x).map_add y₁ y₂)
    (by
      intro r x y
      have hq : q = -p := by omega
      subst q
      refine @intLinear_of_add (M.X (-p)) _ _ _ (M.X (-p)).isModule
        ((ModuleCat.uliftFunctor.{max v w, 0} ℤ).obj
          (ModuleCat.of ℤ (AddCircle (1 : ℚ)))).isModule
        (fun z ↦ ULift.up <| b.eval p x z) ?_ r y
      intro y₁ y₂
      apply ULift.ext
      exact (b.hom p x).map_add y₁ y₂)

/-- A balanced character pairing as a homogeneous pairing into `ℚ/ℤ[0]`. -/
def pairing
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) : TensorProduct.Pairing N M complex.{max v w} :=
  fun p q ↦ if h : p + q = 0 then
    pairingComponent b p q h ≫
      (HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 coefficient.{max v w}
        (p + q) h).inv
    else 0

private theorem apply_cast {I : Type*} {F : I → Type v} {G : I → Type w}
    (f : ∀ i, F i → G i) {i j : I} (h : i = j) (z : F i) :
    f j (cast (congrArg F h) z) = cast (congrArg G h) (f i z) := by
  subst j
  rfl

private theorem single_cast_inv {n : ℤ} (h : n = 0) (z : coefficient.{s}) :
    cast (congrArg (fun j : ℤ ↦ (complex.{s}.X j : Type s)) h)
      ((HomologicalComplex.singleObjXIsoOfEq (up ℤ) 0 coefficient.{s} n h).inv z) =
        z := by
  subst n
  rfl

private theorem pairing_tmul_zero
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) (p q : ℤ) (h : p + q = 0)
    (x : N.X p) (y : M.X q) :
    cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (pairing b p q (x ⊗ₜ[ℤ] y)) =
      ULift.up (b.eval p x
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w)) (rightDegree h)) y)) := by
  simp only [pairing, dif_pos h]
  erw [single_cast_inv h]
  rfl

private theorem cast_comp {F : ℤ → Type s} {i j k : ℤ}
    (h : i = j) (h' : j = k) (z : F i) :
    cast (congrArg F h') (cast (congrArg F h) z) =
      cast (congrArg F (h.trans h')) z := by
  subst j
  subst k
  rfl

private theorem castLinearMap_apply {U : ModuleCat.{v} ℤ} {V V' : ModuleCat.{w} ℤ}
    (h : V = V') (f : U →ₗ[ℤ] V) (z : U) :
    ModuleCat.castLinearMap h f z =
      cast (congrArg (fun X : ModuleCat.{w} ℤ ↦ (X : Type w)) h) (f z) := by
  cases h
  rfl

/-- The homogeneous pairing attached to a balanced character is balanced over `A`. -/
theorem pairing_isBalanced
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) :
    TensorProduct.IsBalanced N M (pairing b) := by
  intro p i q x a y
  by_cases h : (p + i) + q = 0
  · have h' : p + (i + q) = 0 := by omega
    apply (Equiv.cast
      (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)).injective
    change cast
        (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (pairing b (p + i) q (N.smul p i x a ⊗ₜ[ℤ] y)) =
      cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
          (add_assoc p i q).symm)
          (pairing b p (i + q) (x ⊗ₜ[ℤ] M.smul i q a y)))
    erw [pairing_tmul_zero b (p + i) q h]
    erw [cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
      (add_assoc p i q).symm h]
    erw [pairing_tmul_zero b p (i + q) h']
    have hq := rightDegree h
    subst q
    apply congrArg ULift.up
    have hb := congrArg
      (fun c : CharacterModule (M.X (-(p + i))) ↦ c y) (b.balance p i x a)
    dsimp [BalancedPairing.eval,
      LeftDifferentialGradedModule.pontryaginDualSmulValue,
      CharacterModule.dual, CharacterModule.dual_apply]
    change ((b.hom (p + i)) (N.smul p i x a)) y =
      ((b.hom p) x) (ModuleCat.castLinearMap
        (congrArg M.X (LeftDifferentialGradedModule.pontryaginDual_smul_index p i))
        (M.smul i (-(p + i)) a) y) at hb
    erw [castLinearMap_apply] at hb
    exact hb
  · exact (ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 coefficient.{max v w}
        ((p + i) + q) h)).elim _ _

private theorem cast_add {F : ℤ → ModuleCat.{s} ℤ} {i j : ℤ}
    (h : i = j) (x y : F i) :
    cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) x +
        cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) y := by
  subst j
  rfl

private theorem cast_zero {F : ℤ → ModuleCat.{s} ℤ} {i j : ℤ} (h : i = j) :
    cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) (0 : F i) = (0 : F j) := by
  subst j
  rfl

private theorem cast_smul {F : ℤ → ModuleCat.{s} ℤ} {i j : ℤ}
    (h : i = j) (r : ℤ) (z : F i) :
    cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) ((F i).isModule.smul r z) =
      (F j).isModule.smul r
        (cast (congrArg (fun n : ℤ ↦ (F n : Type s)) h) z) := by
  subst j
  rfl

private theorem coefficient_up_smul (r : ℤ) (z : AddCircle (1 : ℚ)) :
    (ULift.up (r • z) : coefficient.{s}) =
      coefficient.{s}.isModule.smul r (ULift.up z) := by
  exact intLinear_of_add (AddCommGroup.toIntModule (AddCircle (1 : ℚ)))
    coefficient.{s}.isModule ULift.up (fun _ _ ↦ rfl) r z

private theorem coefficient_down_smul (r : ℤ) (z : coefficient.{s}) :
    (coefficient.{s}.isModule.smul r z).down = r • z.down := by
  cases z with
  | up z => exact congrArg ULift.down (coefficient_up_smul.{s} r z).symm

private theorem character_smul_apply (P : ModuleCat.{s} ℤ)
    (c : CharacterModule P) (r : ℤ) (z : P) :
    ((CharacterModule.instModule ℤ P).smul r c) z = r • c z := by
  change c (P.isModule.smul r z) = _
  exact intLinear_of_add P.isModule (AddCommGroup.toIntModule (AddCircle (1 : ℚ)))
    c (fun x y ↦ c.map_add x y) r z

private theorem dualD_apply (M : LeftDifferentialGradedModule.{0, w} A)
    (p : ℤ) (c : CharacterModule (M.X (-p))) (y : M.X (-(p + 1))) :
    (LeftDifferentialGradedModule.pontryaginDualD M p c) y =
      (-(p.negOnePow : ℤ)) • c
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w))
          (LeftDifferentialGradedModule.pontryaginDual_d_index p))
          (M.d (-(p + 1)) y)) := by
  change ((CharacterModule.instModule ℤ (M.X (-(p + 1)))).smul
    (-(p.negOnePow : ℤ))
    (CharacterModule.dual (ModuleCat.castLinearMap
      (congrArg M.X (LeftDifferentialGradedModule.pontryaginDual_d_index p))
      (M.d (-(p + 1)))) c)) y = _
  rw [character_smul_apply]
  change (-(p.negOnePow : ℤ)) • c (ModuleCat.castLinearMap
    (congrArg M.X (LeftDifferentialGradedModule.pontryaginDual_d_index p))
    (M.d (-(p + 1))) y) = _
  rw [castLinearMap_apply]

/-- The homogeneous pairing attached to a DG-balanced character commutes with differentials. -/
theorem pairing_isDifferentialCompatible
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) :
    TensorProduct.IsDifferentialCompatible N M (pairing b) := by
  intro p q x y
  by_cases h : (p + q) + 1 = 0
  · have hL : (p + 1) + q = 0 := by omega
    have hR : p + (q + 1) = 0 := by omega
    apply (Equiv.cast
      (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)).injective
    change cast
        (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (complex.{max v w}.d (p + q) ((p + q) + 1)
          (pairing b p q (x ⊗ₜ[ℤ] y))) =
      cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
            (TensorProduct.differentialLeftDegree p q))
            (pairing b (p + 1) q (N.d p x ⊗ₜ[ℤ] y)) +
          (complex.{max v w}.X ((p + q) + 1)).isModule.smul (p.negOnePow : ℤ)
            (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
              (TensorProduct.differentialRightDegree p q))
              (pairing b p (q + 1) (x ⊗ₜ[ℤ] M.d q y))))
    rw [show complex.{max v w}.d (p + q) ((p + q) + 1) = 0 from rfl]
    change cast
        (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (0 : complex.{max v w}.X ((p + q) + 1)) = _
    erw [cast_zero (F := complex.{max v w}.X) h,
      cast_add (F := complex.{max v w}.X) h,
      cast_smul (F := complex.{max v w}.X) h]
    erw [cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
      (TensorProduct.differentialLeftDegree p q) h,
      cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
        (TensorProduct.differentialRightDegree p q) h]
    erw [pairing_tmul_zero b (p + 1) q hL, pairing_tmul_zero b p (q + 1) hR]
    have hq := rightDegree hL
    subst q
    erw [← coefficient_up_smul.{max v w} (p.negOnePow : ℤ)]
    apply ULift.ext
    change (0 : AddCircle (1 : ℚ)) =
      b.eval (p + 1) (N.d p x) y + (p.negOnePow : ℤ) • b.eval p x
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w))
          (LeftDifferentialGradedModule.pontryaginDual_d_index p))
          (M.d (-(p + 1)) y))
    have hb := congrArg (fun c : CharacterModule (M.X (-(p + 1))) ↦ c y)
      (b.comm_d p x)
    rw [dualD_apply] at hb
    change b.eval (p + 1) (N.d p x) y = _ at hb
    rw [hb]
    simp [BalancedPairing.eval]
  · exact (ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 coefficient.{max v w}
        ((p + q) + 1) h)).elim _ _

/-- Descend a DG-balanced character pairing to a cochain map `N ⊗_A M ⟶ ℚ/ℤ[0]`. -/
def ofPairing
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) :
    TensorProduct.complex N M ⟶ complex.{max v w} :=
  TensorProduct.lift N M (pairing b)
    (pairing_isBalanced b) (pairing_isDifferentialCompatible b)

/-- The descended tensor character agrees with its pairing on homogeneous pure tensors. -/
theorem ofPairing_tmul
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) (p q : ℤ) (x : N.X p) (y : M.X q) :
    (ofPairing b).f (p + q) (TensorProduct.tmul N M x y) =
      pairing b p q (x ⊗ₜ[ℤ] y) :=
  TensorProduct.lift_tmul N M (pairing b)
    (pairing_isBalanced b) (pairing_isDifferentialCompatible b) p q x y

/-- Evaluate a tensor character on a homogeneous pure tensor of total degree zero. -/
def toPairingValue
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x : N.X p) (y : M.X (-p)) : AddCircle (1 : ℚ) :=
  (HomologicalComplex.singleObjXSelf (up ℤ) 0 coefficient.{max v w}).hom
    (f.f 0 <| cast
      (congrArg (fun n : ℤ ↦ (TensorProduct.family N M n : Type (max v w)))
        (complementaryDegree p))
      (TensorProduct.tmul N M x y)) |>.down

private theorem toPairingValue_cast
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p q : ℤ) (h : p + q = 0) (x : N.X p) (y : M.X q) :
    toPairingValue f p x
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w)) (rightDegree h)) y) =
      (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h)
        (f.f (p + q) (TensorProduct.tmul N M x y))).down := by
  have hq := rightDegree h
  subst q
  unfold toPairingValue
  erw [apply_cast (fun n z ↦ f.f n z) (complementaryDegree p)]
  rfl

private theorem toPairingValue_d_relation
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x : N.X p) (y : M.X (-(p + 1))) :
    toPairingValue f (p + 1) (N.d p x) y +
      (p.negOnePow : ℤ) • toPairingValue f p x
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w))
          (LeftDifferentialGradedModule.pontryaginDual_d_index p))
          (M.d (-(p + 1)) y)) = 0 := by
  let q := -(p + 1)
  have h : (p + q) + 1 = 0 := by dsimp [q]; omega
  have hL : (p + 1) + q = 0 := by dsimp [q]; omega
  have hR : p + (q + 1) = 0 := by dsimp [q]; omega
  letI : Module ℤ (TensorProduct.family N M ((p + q) + 1)) :=
    (TensorProduct.family N M ((p + q) + 1)).isModule
  letI : Module ℤ (complex.{max v w}.X ((p + q) + 1)) :=
    (complex.{max v w}.X ((p + q) + 1)).isModule
  have hc := congrArg (fun g : (TensorProduct.complex N M).X (p + q) ⟶
    complex.{max v w}.X ((p + q) + 1) ↦ g (TensorProduct.tmul N M x y))
    (f.comm (p + q) ((p + q) + 1))
  change complex.{max v w}.d (p + q) ((p + q) + 1)
      (f.f (p + q) (TensorProduct.tmul N M x y)) =
    f.f ((p + q) + 1)
      ((TensorProduct.complex N M).d (p + q) ((p + q) + 1)
        (TensorProduct.tmul N M x y)) at hc
  rw [show complex.{max v w}.d (p + q) ((p + q) + 1) = 0 from rfl,
    TensorProduct.d_tmul N M p q x y] at hc
  change (0 : complex.{max v w}.X ((p + q) + 1)) = _ at hc
  erw [map_add, (f.f ((p + q) + 1)).hom.map_smul] at hc
  erw [apply_cast (fun n z ↦ f.f n z) (TensorProduct.differentialLeftDegree p q),
    apply_cast (fun n z ↦ f.f n z) (TensorProduct.differentialRightDegree p q)] at hc
  have hc0 := congrArg (fun z : complex.{max v w}.X ((p + q) + 1) ↦
    cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) h) z) hc
  erw [cast_zero (F := complex.{max v w}.X) h,
    cast_add (F := complex.{max v w}.X) h,
    cast_smul (F := complex.{max v w}.X) h,
    cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
      (TensorProduct.differentialLeftDegree p q) h,
    cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
      (TensorProduct.differentialRightDegree p q) h] at hc0
  have hcd := congrArg (fun z : coefficient.{max v w} ↦ z.down) hc0
  change (0 : AddCircle (1 : ℚ)) =
    (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) hL)
      (f.f ((p + 1) + q) (TensorProduct.tmul N M (N.d p x) y))).down +
    (coefficient.{max v w}.isModule.smul (p.negOnePow : ℤ)
      (cast (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w))) hR)
        (f.f (p + (q + 1)) (TensorProduct.tmul N M x (M.d q y))))).down at hcd
  rw [coefficient_down_smul] at hcd
  erw [← toPairingValue_cast f (p + 1) q hL,
    ← toPairingValue_cast f p (q + 1) hR] at hcd
  exact hcd.symm

private theorem toPairingValue_add_right
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x : N.X p) (y₁ y₂ : M.X (-p)) :
    toPairingValue f p x (y₁ + y₂) =
      toPairingValue f p x y₁ + toPairingValue f p x y₂ := by
  letI : Module ℤ (TensorProduct.family N M (p + -p)) :=
    (TensorProduct.family N M (p + -p)).isModule
  letI : Module ℤ (TensorProduct.family N M 0) :=
    (TensorProduct.family N M 0).isModule
  letI : Module ℤ (complex.{max v w}.X 0) := (complex.{max v w}.X 0).isModule
  letI : Module ℤ coefficient.{max v w} := coefficient.{max v w}.isModule
  unfold toPairingValue
  rw [show TensorProduct.tmul N M x (y₁ + y₂) =
      TensorProduct.tmul N M x y₁ + TensorProduct.tmul N M x y₂ from
    (TensorProduct.tmulRight N M x).map_add y₁ y₂]
  erw [cast_add (F := TensorProduct.family N M) (complementaryDegree p)]
  erw [map_add, map_add]
  rfl

private theorem toPairingValue_add_left
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x₁ x₂ : N.X p) (y : M.X (-p)) :
    toPairingValue f p (x₁ + x₂) y =
      toPairingValue f p x₁ y + toPairingValue f p x₂ y := by
  letI : Module ℤ (TensorProduct.family N M (p + -p)) :=
    (TensorProduct.family N M (p + -p)).isModule
  letI : Module ℤ (TensorProduct.family N M 0) :=
    (TensorProduct.family N M 0).isModule
  letI : Module ℤ (complex.{max v w}.X 0) := (complex.{max v w}.X 0).isModule
  letI : Module ℤ coefficient.{max v w} := coefficient.{max v w}.isModule
  unfold toPairingValue
  rw [show TensorProduct.tmul N M (x₁ + x₂) y =
      TensorProduct.tmul N M x₁ y + TensorProduct.tmul N M x₂ y from
    (TensorProduct.tmulLeft N M y).map_add x₁ x₂]
  erw [cast_add (F := TensorProduct.family N M) (complementaryDegree p)]
  erw [map_add, map_add]
  rfl

/-- Evaluation of a tensor character in one right-module degree. -/
def toPairingComponent
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w}) (p : ℤ) :
    BalancedPairing.Component N M p :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ)
    (N.X p) (CharacterModule (M.X (-p))) _ _ (N.X p).isModule
      (CharacterModule.instModule ℤ (M.X (-p)))
    { toFun := fun x ↦
        { toFun := toPairingValue f p x
          map_zero' := by
            letI : Module ℤ (TensorProduct.family N M (p + -p)) :=
              (TensorProduct.family N M (p + -p)).isModule
            letI : Module ℤ (TensorProduct.family N M 0) :=
              (TensorProduct.family N M 0).isModule
            letI : Module ℤ (complex.{max v w}.X 0) := (complex.{max v w}.X 0).isModule
            letI : Module ℤ coefficient.{max v w} := coefficient.{max v w}.isModule
            unfold toPairingValue
            rw [show TensorProduct.tmul N M x (0 : M.X (-p)) = 0 from
              (TensorProduct.tmulRight N M x).map_zero]
            erw [cast_zero (F := TensorProduct.family N M) (complementaryDegree p)]
            erw [map_zero, map_zero]
            rfl
          map_add' := by exact toPairingValue_add_right f p x }
      map_add' := by
        intro x₁ x₂
        apply CharacterModule.ext
        exact toPairingValue_add_left f p x₁ x₂ }
    (by
      intro r x
      apply CharacterModule.ext
      intro y
      change toPairingValue f p ((N.X p).isModule.smul r x) y =
        toPairingValue f p x ((M.X (-p)).isModule.smul r y)
      exact (intLinear_of_add (N.X p).isModule
        (AddCommGroup.toIntModule (AddCircle (1 : ℚ)))
        (fun z ↦ toPairingValue f p z y)
        (fun x₁ x₂ ↦ toPairingValue_add_left f p x₁ x₂ y) r x).trans
        (intLinear_of_add (M.X (-p)).isModule
          (AddCommGroup.toIntModule (AddCircle (1 : ℚ)))
          (toPairingValue f p x) (toPairingValue_add_right f p x) r y).symm)

/-- A cochain map `N ⊗_A M ⟶ ℚ/ℤ[0]` induces its DG-balanced character pairing. -/
def toPairing
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w}) : BalancedPairing N M where
  hom := toPairingComponent f
  comm_d := by
    intro p x
    apply CharacterModule.ext
    intro y
    change toPairingValue f (p + 1) (N.d p x) y =
      (LeftDifferentialGradedModule.pontryaginDualD M p (toPairingComponent f p x)) y
    rw [dualD_apply]
    change toPairingValue f (p + 1) (N.d p x) y =
      (-(p.negOnePow : ℤ)) • toPairingValue f p x
        (cast (congrArg (fun n : ℤ ↦ (M.X n : Type w))
          (LeftDifferentialGradedModule.pontryaginDual_d_index p))
          (M.d (-(p + 1)) y))
    simpa only [neg_smul] using
      eq_neg_of_add_eq_zero_left (toPairingValue_d_relation f p x y)
  balance := by
    intro p i x a
    apply CharacterModule.ext
    intro y
    change toPairingValue f (p + i) (N.smul p i x a) y =
      toPairingValue f p x (ModuleCat.castLinearMap
        (congrArg M.X (LeftDifferentialGradedModule.pontryaginDual_smul_index p i))
        (M.smul i (-(p + i)) a) y)
    erw [castLinearMap_apply]
    have h' : p + (i + -(p + i)) = 0 := by omega
    erw [toPairingValue_cast f p (i + -(p + i)) h']
    unfold toPairingValue
    erw [apply_cast (fun n z ↦ f.f n z) (complementaryDegree (p + i))]
    rw [TensorProduct.tmul_smul N M p i (-(p + i)) x a y]
    erw [apply_cast (fun n z ↦ f.f n z) (add_assoc p i (-(p + i))).symm]
    erw [cast_comp (F := fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
      (add_assoc p i (-(p + i))).symm (complementaryDegree (p + i))]

/-- Evaluation of the pairing recovered from a tensor character is evaluation on a pure tensor. -/
@[simp]
theorem toPairing_eval
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x : N.X p) (y : M.X (-p)) :
    (toPairing f).eval p x y = toPairingValue f p x y := by
  rfl

private theorem toPairingValue_ofPairing
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) (p : ℤ) (x : N.X p) (y : M.X (-p)) :
    toPairingValue (ofPairing b) p x y = b.eval p x y := by
  unfold toPairingValue
  erw [apply_cast (fun n z ↦ (ofPairing b).f n z) (complementaryDegree p)]
  rw [ofPairing_tmul]
  erw [pairing_tmul_zero b p (-p) (complementaryDegree p)]
  rfl

/-- DG-balanced pairings are canonically the cochain maps `N ⊗_A M ⟶ ℚ/ℤ[0]`. -/
@[stacks 09K3 "tensor characters and differential graded balanced pairings"]
def pairingEquiv
    (N : DifferentialGradedModule.{0, v} A)
    (M : LeftDifferentialGradedModule.{0, w} A) :
    BalancedPairing N M ≃
      (TensorProduct.complex N M ⟶ complex.{max v w}) where
  toFun := ofPairing
  invFun := toPairing
  left_inv := by
    intro b
    apply BalancedPairing.ext
    intro p x y
    exact toPairingValue_ofPairing b p x y
  right_inv := by
    intro f
    apply TensorProduct.hom_ext N M
    intro p q x y
    by_cases h : p + q = 0
    · have hq := rightDegree h
      subst q
      apply (Equiv.cast
        (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
          (complementaryDegree p))).injective
      change cast
          (congrArg (fun n : ℤ ↦ (complex.{max v w}.X n : Type (max v w)))
            (complementaryDegree p))
          ((ofPairing (toPairing f)).f (p + -p) (TensorProduct.tmul N M x y)) = _
      rw [ofPairing_tmul]
      erw [pairing_tmul_zero (toPairing f) p (-p) (complementaryDegree p)]
      apply ULift.ext
      change toPairingValue f p x y = _
      unfold toPairingValue
      erw [apply_cast (fun n z ↦ f.f n z) (complementaryDegree p)]
      rfl
    · have hz := HomologicalComplex.isZero_single_obj_X (up ℤ)
        0 coefficient.{max v w} (p + q) h
      exact congrArg (fun g : TensorProduct.family N M (p + q) ⟶
        complex.{max v w}.X (p + q) ↦ g (TensorProduct.tmul N M x y))
        (hz.eq_of_tgt ((ofPairing (toPairing f)).f (p + q)) (f.f (p + q)))

/-- Lemma 22.19.2 (09K3): morphisms into a Pontryagin dual are canonically cochain maps
`N ⊗_A M ⟶ ℚ/ℤ[0]`. -/
@[stacks 09K3 "tensor-character adjunction"]
def homEquiv
    (N : DifferentialGradedModule.{0, v} A)
    (M : LeftDifferentialGradedModule.{0, w} A) :
    DifferentialGradedModule.Hom N
      (LeftDifferentialGradedModule.pontryaginDual M) ≃
        (TensorProduct.complex N M ⟶ complex.{max v w}) :=
  (BalancedPairing.homEquiv N M).trans (pairingEquiv N M)

end DifferentialGradedModule.TensorCharacter
