/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Maximal-adic truncations of complete local algebras -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- Spectrum of the order-`N` maximal-adic truncation `R ⧸ m ^ N`. -/
def powSpec (R : CompleteLocalSAlgebra S) (N : ℕ) : Scheme.{u} :=
  Spec (.of (R.carrier ⧸ maximalIdeal R.carrier ^ N))

/-- `powSpec` is the spectrum of the order-`N` quotient by the maximal ideal. -/
theorem powSpec_eq (R : CompleteLocalSAlgebra S) (N : ℕ) :
    R.powSpec N = Spec (.of (R.carrier ⧸ maximalIdeal R.carrier ^ N)) :=
  sorry

/-- Structure morphism `Spec(R ⧸ m ^ N) ⟶ S` of an order-`N` truncation. -/
def powToS (R : CompleteLocalSAlgebra S) (N : ℕ) : R.powSpec N ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ N))) ≫ R.toS

/-- The structure map of an order-`N` truncation is the spectrum of the quotient
map followed by `toS`. -/
theorem powToS_eq (R : CompleteLocalSAlgebra S) (N : ℕ) :
    R.powToS N =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ N))) ≫
        R.toS :=
  sorry

/-- Restriction morphism `Spec(R ⧸ m ^ N) ⟶ Spec(R)` in `Over S`. -/
def powOverHom (R : CompleteLocalSAlgebra S) (N : ℕ) :
    Over.mk (R.powToS N) ⟶ Over.mk R.toS :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ N)))) rfl

/-- The underlying scheme morphism of `powOverHom` is the spectrum of the
order-`N` quotient map. -/
theorem powOverHom_left (R : CompleteLocalSAlgebra S) (N : ℕ) :
    (R.powOverHom N).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ N))) :=
  sorry

/-- The structure morphism of `powOverHom` recovers `powToS`. -/
theorem powToS_comp (R : CompleteLocalSAlgebra S) (N : ℕ) :
    (R.powOverHom N).left ≫ R.toS = R.powToS N :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra

