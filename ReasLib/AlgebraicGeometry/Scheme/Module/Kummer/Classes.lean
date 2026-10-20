/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Pairs

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry RingedSpace
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kummer

/-- Compatible-isomorphism classes of invertible modules with a chosen power trivialization. -/
abbrev Classes (S : Scheme.{u}) (n : ℕ) := Quotient (pairSetoid S n)

/-- The compatible-isomorphism class of an equipped pair. -/
def classOf {S : Scheme.{u}} {n : ℕ} (P : Pair S n) : Classes S n := Quotient.mk'' P

/-- Equality of equipped-pair classes is precisely compatible isomorphism. -/
theorem class_eq_iff {S : Scheme.{u}} {n : ℕ} (P Q : Pair S n) :
    classOf P = classOf Q ↔ Nonempty (PairIso P Q) := sorry

/-- Every equipped-pair class has a representative. -/
theorem class_surjective {S : Scheme.{u}} {n : ℕ} :
    Function.Surjective (classOf (S := S) (n := n)) := sorry

namespace Classes

variable {S : Scheme.{u}} {n : ℕ}

/-- Addition of equipped-pair classes is induced by tensor product. -/
def add (x y : Classes S n) : Classes S n :=
  Quotient.liftOn₂ x y (fun P Q ↦ classOf (P.tensor Q))
    (fun _ _ _ _ h k ↦ h.elim (fun e ↦ k.elim (fun f ↦
      Quotient.sound (Pair.tensor_respects_iso e f))))

/-- The zero class is represented by the trivial pair. -/
def zero (S : Scheme.{u}) (n : ℕ) : Classes S n := classOf (Pair.unit S n)

/-- Negation of equipped-pair classes is induced by dualization. -/
def neg (x : Classes S n) : Classes S n :=
  Quotient.liftOn x (fun P ↦ classOf P.dual)
    (fun _ _ h ↦ h.elim (fun e ↦ Quotient.sound (Pair.dual_respects_iso e)))

/-- Tensor-product addition is associative on compatible-isomorphism classes. -/
theorem add_assoc (x y z : Classes S n) : add (add x y) z = add x (add y z) := sorry

/-- The trivial-pair class is a left identity for tensor-product addition. -/
theorem zero_add (x : Classes S n) : add (zero S n) x = x := sorry

/-- The trivial-pair class is a right identity for tensor-product addition. -/
theorem add_zero (x : Classes S n) : add x (zero S n) = x := sorry

/-- Tensor-product addition is commutative on compatible-isomorphism classes. -/
theorem add_comm (x y : Classes S n) : add x y = add y x := sorry

/-- The dual-pair class is an additive inverse. -/
theorem neg_add_cancel (x : Classes S n) : add (neg x) x = zero S n := sorry

/-- Equipped-pair classes form the canonical tensor-product additive commutative group. -/
instance instAddCommGroup (S : Scheme.{u}) (n : ℕ) : AddCommGroup (Classes S n) where
  add := add
  zero := zero S n
  neg := neg
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := @nsmulRec (Classes S n) ⟨zero S n⟩ ⟨add⟩
  zsmul := @zsmulRec (Classes S n) ⟨zero S n⟩ ⟨add⟩ ⟨neg⟩
    (@nsmulRec (Classes S n) ⟨zero S n⟩ ⟨add⟩)

end Classes

/-- Tensor product has the tensor-product underlying module and represents addition of classes. -/
theorem class_tensor_spec {S : Scheme.{u}} {n : ℕ} (P Q : Pair S n) :
    (P.tensor Q).lineBundle = P.lineBundle ⊗ Q.lineBundle ∧
      classOf (P.tensor Q) = classOf P + classOf Q := sorry

end AlgebraicGeometry.Scheme.Modules.Kummer
