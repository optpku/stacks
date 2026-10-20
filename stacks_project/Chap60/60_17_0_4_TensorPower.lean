/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

universe u

/-- A concrete iterated tensor-product stage over a commutative ring `A`. -/
structure TensorPowerStage.{w} (A : Type u) [CommRing A] where
  carrier : Type w
  commRing : CommRing carrier
  algebra : Algebra A carrier

/-- The stage at zero is one polynomial copy; each successor adds one copy on the left. -/
noncomputable def tensorPowerStage
    (A : Type u) [CommRing A] (ι : Type u) : ℕ → TensorPowerStage A
  | 0 =>
      { carrier := MvPolynomial ι A
        commRing := inferInstance
        algebra := inferInstance }
  | n + 1 =>
      let previous := tensorPowerStage A ι n
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : CommRing previous.carrier := previous.commRing
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : Algebra A previous.carrier := previous.algebra
      { carrier := TensorProduct A (MvPolynomial ι A) previous.carrier
        commRing := inferInstance
        algebra := inferInstance }

/-- The carrier of the concrete iterated tensor-product stage. -/
abbrev tensorPowerCarrier
    (A : Type u) [CommRing A] (ι : Type u) (n : ℕ) : Type u :=
  (tensorPowerStage A ι n).carrier

/-- The canonical commutative-ring structure on an iterated tensor stage. -/
noncomputable instance tensorPowerCarrier.commRing
    (A : Type u) [CommRing A] (ι : Type u) (n : ℕ) :
    CommRing (tensorPowerCarrier A ι n) :=
  (tensorPowerStage A ι n).commRing

/-- The canonical `A`-algebra structure on an iterated tensor stage. -/
noncomputable instance tensorPowerCarrier.algebra
    (A : Type u) [CommRing A] (ι : Type u) (n : ℕ) :
    Algebra A (tensorPowerCarrier A ι n) :=
  (tensorPowerStage A ι n).algebra

/-- The canonical algebra map from the iterated tensor stage to `C`, induced recursively from `π`. -/
noncomputable def tensorPowerAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (n : ℕ) :
    tensorPowerCarrier A ι n →ₐ[A] C :=
  match n with
  | 0 => π
  | n + 1 =>
      Algebra.TensorProduct.productMap π (tensorPowerAlgHom π n)
