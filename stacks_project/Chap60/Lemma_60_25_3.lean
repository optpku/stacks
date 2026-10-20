/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Inseparable
import StacksCheckRecall

public section

open CategoryTheory
open DPPolynomial.DeRham

universe u

/- Lemma 60.25.3. The completed inseparable comparison admits one reverse map with
both composites homotopic to multiplication by p. Taking B to be the uncompleted
polynomial divided-power envelope makes its completion the ring D of the source. -/
@[stacks 07N1] #check
  (Connection.Adic.existsInseparableReverseComparisonHomotopy :
    ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
      {J : Ideal B} (δ : DividedPowers J) (p : ℕ) (lam : completedRingB B p)
      {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]
      [Fact p.Prime] [Algebra (Int.LocalizationAtPrime p) B]
      (h_nilpotent : IsNilpotent (p : B ⧸ J))
      [IsAdicComplete (principalIdealB (completedRingB B p) p) M]
      (conn : Connection.Adic A B δ p M)
      (hconn : Connection.Adic.IsIntegrable A B δ p conn),
      ∃ e : Connection.Adic.inseparableComplex A B δ p lam conn hconn ⟶
          Connection.Adic.deRhamComplex A B δ p conn hconn,
        Nonempty (Homotopy (Connection.Adic.inseparableComparison A B δ p lam conn hconn ≫ e)
          (p • 𝟙 (Connection.Adic.deRhamComplex A B δ p conn hconn))) ∧
        Nonempty (Homotopy (e ≫ Connection.Adic.inseparableComparison A B δ p lam conn hconn)
          (p • 𝟙 (Connection.Adic.inseparableComplex A B δ p lam conn hconn))))

