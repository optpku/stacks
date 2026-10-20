/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.TensorProduct
public import ReasLib.Algebra.CentralSimple.BaseChange
public import ReasLib.Algebra.CentralSimple.Azumaya
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-! # Brauer Group Structure

The commutative group structure on the Brauer group `Br(k)` of a field `k`,
with multiplication induced by tensor product and inverse by the opposite algebra.

## Main declarations

- `CSA.opposite` — opposite algebra as CSA
- `CSA.unit` — neutral element representative
- `CSA.brauerEquivalent_of_algEquiv` — algebra equivalence implies Brauer equivalence
- `CSA.tensorProduct_opposite_algEquiv` — A ⊗ Aᵒᵖ ≅ Mₙ(unit k)
- `CSA.brauerEquivalent_opposite` — compatibility with opposite
- `CSA.brauerEquivalent_tensorProduct` — compatibility with tensor product
- `CSA.brauerEquivalent_assoc` — associativity
- `CSA.brauerEquivalent_comm` — commutativity
- `CSA.brauerEquivalent_one_right` — right unit law
- `CSA.brauerEquivalent_one_left` — left unit law
- `CSA.brauerEquivalent_inv` — inverse law
- `Br` — abbreviation for `BrauerGroup`
- `CommGroup (Br(k))` — the Brauer group is a commutative group

## References

- [Stacks Project, Tag 074L](https://stacks.math.columbia.edu/tag/074L)

@stack 074L
-/

@[expose] public section

noncomputable section

open Matrix
open scoped TensorProduct

universe u v

/-- The Brauer group of `k`, realized as the quotient of finite-dimensional central simple
`k`-algebras by Brauer equivalence in universe `max u v`. -/
abbrev Br (k : Type u) [Field k] := BrauerGroup.{u, max u v} k

notation "Br(" k ")" => Br k

namespace CSA

variable {k : Type u} [Field k]

/-- The canonical `1 × 1` matrix algebra is algebraically equivalent to the underlying
`k`-algebra. -/
def matrixOneAlgEquiv (A : Type v) [Semiring A] [Algebra k A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[k] A :=
  (Matrix.reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv

/-- An actual algebra equivalence already gives a Brauer equivalence by using
`1 × 1` matrix stabilizations on both sides. -/
theorem brauerEquivalent_of_algEquiv {A B : CSA.{u, v} k} (e : A ≃ₐ[k] B) :
    IsBrauerEquivalent A B := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  refine ⟨(matrixOneAlgEquiv (k := k) A).trans <| e.trans <| (matrixOneAlgEquiv (k := k) B).symm⟩

/-- The opposite algebra of a finite-dimensional central simple `k`-algebra, repackaged as the
canonical corresponding object of `CSA k`. -/
def opposite (A : CSA.{u, v} k) : CSA.{u, v} k where
  toAlgCat := AlgCat.of k Aᵐᵒᵖ

variable (k : Type u) [Field k]

/-- The canonical `ULift` representative of the neutral Brauer class in carrier universe
`max u v`. -/
def unit : CSA.{u, max u v} k where
  toAlgCat := AlgCat.of k (ULift.{v, u} k)
  isCentral := by
    refine ⟨fun x _ ↦ ?_⟩
    exact ⟨x.down, rfl⟩
  isSimple := inferInstance
  fin_dim := by
    simpa using
      (ULift.algEquiv : ULift.{v, u} k ≃ₐ[k] k).symm.toLinearEquiv.finiteDimensional

/-- The carrier of the neutral representative is canonically identified with the base field. -/
private def unitCarrierAlgEquiv (k : Type u) [Field k] :
    ↑(unit k).toAlgCat ≃ₐ[k] k :=
  ULift.algEquiv

/-- `A ⊗[k] Aᵐᵒᵖ` is identified with a full matrix algebra over the canonical neutral
representative through the Azumaya endomorphism model of `A`. -/
theorem tensorProduct_opposite_algEquiv (A : CSA.{u, v} k) :
    Nonempty <|
      A ⊗[k] Aᵐᵒᵖ ≃ₐ[k]
        Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) ↑(unit k).toAlgCat := by
  let eEnd : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A :=
    AlgEquiv.ofBijective (AlgHom.mulLeftRight k A) (IsAzumaya.AlgHom.mulLeftRight_bij (R := k) (A := A))
  let b : Module.Basis (Fin (Module.finrank k A)) k A := Module.finBasis k A
  let eMatrix : Module.End k A ≃ₐ[k] Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) k :=
    algEquivMatrix b
  let eULift :
    Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) k ≃ₐ[k]
        Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) ↑(unit k).toAlgCat :=
    (unitCarrierAlgEquiv (k := k)).symm.mapMatrix
  exact ⟨eEnd.trans <| eMatrix.trans eULift⟩

variable {k}

/-- Brauer equivalence is compatible with passage to opposite algebras. -/
theorem brauerEquivalent_opposite {A B : CSA.{u, v} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent A.opposite B.opposite := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  refine ⟨AlgEquiv.mopMatrix.trans <| (AlgEquiv.op e).trans AlgEquiv.mopMatrix.symm⟩

/-- Brauer equivalence is compatible with tensor product on representatives. -/
theorem brauerEquivalent_tensorProduct {A A' B B' : CSA.{u, v} k}
    (hAA' : IsBrauerEquivalent A A') (hBB' : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (A.tensorProduct B) (A'.tensorProduct B') := by
  obtain ⟨n, m, hn, hm, ⟨eA⟩⟩ := hAA'
  obtain ⟨p, q, hp, hq, ⟨eB⟩⟩ := hBB'
  refine ⟨n * p, m * q, Nat.mul_ne_zero hn hp, Nat.mul_ne_zero hm hq, ?_⟩
  refine ⟨(Matrix.reindexAlgEquiv k (A.tensorProduct B) finProdFinEquiv).symm.trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) k k A B).symm.trans <|
    (Algebra.TensorProduct.congr eA eB).trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin q) k k A' B').trans <|
    Matrix.reindexAlgEquiv k (A'.tensorProduct B') finProdFinEquiv⟩

/-- Tensor product on representatives induces the associative law in the Brauer group. -/
theorem brauerEquivalent_assoc (A B C : CSA.{u, v} k) :
    IsBrauerEquivalent ((A.tensorProduct B).tensorProduct C) (A.tensorProduct (B.tensorProduct C)) :=
  by
  exact brauerEquivalent_of_algEquiv
    (Algebra.TensorProduct.assoc k k k A B C)

/-- Tensor product on representatives induces the commutative law in the Brauer group. -/
theorem brauerEquivalent_comm (A B : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct B) (B.tensorProduct A) := by
  exact brauerEquivalent_of_algEquiv (Algebra.TensorProduct.comm k A B)

/-- Tensoring with the canonical neutral representative leaves a Brauer class unchanged. -/
theorem brauerEquivalent_one_right (A : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct (unit k)) A := by
  let eUnit : A.tensorProduct (unit k) ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr ((AlgEquiv.refl : A ≃ₐ[k] A))
      (unitCarrierAlgEquiv (k := k))).trans <|
        Algebra.TensorProduct.rid k k A
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) (A.tensorProduct (unit k))).trans <|
    eUnit.trans <| (matrixOneAlgEquiv (k := k) A).symm⟩

/-- The canonical neutral representative is a left unit for tensor product on Brauer classes. -/
theorem brauerEquivalent_one_left (A : CSA.{u, v} k) :
    IsBrauerEquivalent ((unit k).tensorProduct A) A := by
  let eUnit : (unit k).tensorProduct A ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr (unitCarrierAlgEquiv (k := k))
      ((AlgEquiv.refl : A ≃ₐ[k] A))).trans <|
        Algebra.TensorProduct.lid k A
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) ((unit k).tensorProduct A)).trans <|
    eUnit.trans <| (matrixOneAlgEquiv (k := k) A).symm⟩

/-- The opposite algebra represents the inverse Brauer class. -/
theorem brauerEquivalent_inv (A : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct A.opposite) (unit k) := by
  obtain ⟨e⟩ := tensorProduct_opposite_algEquiv (k := k) A
  have hfinrank : Module.finrank k A ≠ 0 := by
    exact Nat.ne_of_gt (Module.finrank_pos (R := k) (M := A))
  refine ⟨1, Module.finrank k A, one_ne_zero, hfinrank, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) (A.tensorProduct A.opposite)).trans e⟩

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k]

/-- Two finite-dimensional central simple `k`-algebras are Brauer equivalent when
positive-size matrix algebras over them are algebraically equivalent. -/
abbrev IsBrauerEquivalent (A B : CSA.{u, v} k) : Prop :=
  _root_.IsBrauerEquivalent A B

/-- The Brauer group `Br(k)` of `k` is the quotient `BrauerGroup k` of finite-dimensional central
simple `k`-algebras by Brauer equivalence, with multiplication induced by tensor product and
inverse induced by the opposite algebra. -/
@[stacks 074L]
noncomputable instance : One (Br(k)) :=
  ⟨Quotient.mk _ (CSA.unit k)⟩

/-- Multiplication in the Brauer group is induced by tensor product of representatives. -/
noncomputable instance : Mul (Br(k)) :=
  ⟨Quotient.map₂ CSA.tensorProduct
      fun {_ _} h₁ {_ _} h₂ ↦ CSA.brauerEquivalent_tensorProduct h₁ h₂⟩

/-- Inversion in the Brauer group is induced by passage to the opposite algebra. -/
noncomputable instance : Inv (Br(k)) :=
  ⟨Quotient.map CSA.opposite fun _ _ h ↦ CSA.brauerEquivalent_opposite h⟩

/-- The quotient `Br(k)` carries the canonical commutative-group structure induced by tensor
product, the opposite algebra, and the neutral representative. -/
@[stacks 074L]
noncomputable instance instCommGroupBr : CommGroup (Br(k)) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun A B C ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_assoc A B C)
  one_mul a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_one_left A)
  mul_one a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_one_right A)
  inv_mul_cancel a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound <|
      IsBrauerEquivalent.trans (CSA.brauerEquivalent_comm A.opposite A)
        (CSA.brauerEquivalent_inv A)
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b fun A B ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_comm A B)

@[simp] theorem one_def :
    (1 : Br(k)) = Quotient.mk _ (CSA.unit k) :=
  rfl

@[simp] theorem mk_mul_mk (A B : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k)) * Quotient.mk _ B =
      Quotient.mk _ (A.tensorProduct B) :=
  rfl

@[simp] theorem mk_inv (A : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k))⁻¹ = Quotient.mk _ A.opposite :=
  rfl

end BrauerGroup

end
