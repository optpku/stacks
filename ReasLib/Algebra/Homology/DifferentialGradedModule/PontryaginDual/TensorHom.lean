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
theorem complementaryDegree (p : ℤ) : p + -p = 0 := sorry

/-- Recover the complementary degree from a total-degree-zero decomposition. -/
theorem rightDegree {p q : ℤ} (h : p + q = 0) : q = -p := sorry

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
    sorry sorry sorry sorry

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

/-- The homogeneous pairing attached to a balanced character is balanced over `A`. -/
theorem pairing_isBalanced
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) :
    TensorProduct.IsBalanced N M (pairing b) := sorry

/-- The homogeneous pairing attached to a DG-balanced character commutes with differentials. -/
theorem pairing_isDifferentialCompatible
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (b : BalancedPairing N M) :
    TensorProduct.IsDifferentialCompatible N M (pairing b) := sorry

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
      pairing b p q (x ⊗ₜ[ℤ] y) := sorry

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
          map_zero' := sorry
          map_add' := sorry }
      map_add' := sorry }
    sorry

/-- A cochain map `N ⊗_A M ⟶ ℚ/ℤ[0]` induces its DG-balanced character pairing. -/
def toPairing
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w}) : BalancedPairing N M where
  hom := toPairingComponent f
  comm_d := sorry
  balance := sorry

/-- Evaluation of the pairing recovered from a tensor character is evaluation on a pure tensor. -/
@[simp]
theorem toPairing_eval
    {N : DifferentialGradedModule.{0, v} A}
    {M : LeftDifferentialGradedModule.{0, w} A}
    (f : TensorProduct.complex N M ⟶ complex.{max v w})
    (p : ℤ) (x : N.X p) (y : M.X (-p)) :
    (toPairing f).eval p x y = toPairingValue f p x y := sorry

/-- DG-balanced pairings are canonically the cochain maps `N ⊗_A M ⟶ ℚ/ℤ[0]`. -/
@[stacks 09K3 "tensor characters and differential graded balanced pairings"]
def pairingEquiv
    (N : DifferentialGradedModule.{0, v} A)
    (M : LeftDifferentialGradedModule.{0, w} A) :
    BalancedPairing N M ≃
      (TensorProduct.complex N M ⟶ complex.{max v w}) where
  toFun := ofPairing
  invFun := toPairing
  left_inv := sorry
  right_inv := sorry

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
