/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Completion.CohenRing
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.RegularLocalRing.Fiber
public import ReasLib.RingTheory.RegularLocalRing.Flatness
public import ReasLib.RingTheory.RegularLocalRing.Parameters
import Mathlib.Tactic.CrossRefAttribute

/-!
# Power Series Presentations of Complete Local Homomorphisms

A local homomorphism of Noetherian complete local rings admits compatible power series
presentations.  The coefficient rings are fields in equal characteristic and Cohen rings in mixed
characteristic.  The comparison map is flat and has regular closed fiber.

@stack 07NN
-/

@[expose] public section

open IsLocalRing
open CategoryTheory CommRingCat

universe u

/-- Lemma 15.39.3 (Stacks `07NN`): a local homomorphism `A → B` of Noetherian complete local
rings has a commutative surjective presentation by finite-variable power series rings.  A regular
system of parameters on the source maps to part of one on the target, and the comparison map is
flat with regular closed fiber.  The coefficient rings are fields in equal characteristic and
Cohen rings in positive residue characteristic. -/
@[stacks 07NN "compatible power series presentation"]
theorem exists_powerSeries_presentation_of_localHom_completeLocal
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] [IsLocalHom f] :
    (∃ _ : ringChar A = ringChar (ResidueField A),
      ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
        (K L : Type u) (_ : Field K) (_ : Field L),
        let P := MvPowerSeries σ K
        let Q := MvPowerSeries τ L
        ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
          -- Local instance justification (instance diamond): orient the comparison algebra by the
          -- chosen vertical ring homomorphism only inside this presentation branch.
          let _ : Algebra P Q := rToS.toAlgebra
          Function.Surjective rToA ∧
            Function.Surjective sToB ∧
            CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
            (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
              (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                  (∀ i, rToS (x i : P) = (z i : Q)) ∧
                  IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
            rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q))
      ∨
      ∃ (p : ℕ) (_ : Nat.Prime p), CharP (ResidueField A) p ∧
        ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
          (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
          (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
          let P := MvPowerSeries σ R₀
          let Q := MvPowerSeries τ S₀
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            -- Local instance justification (instance diamond): orient the mixed-characteristic
            -- comparison algebra by the chosen vertical map only inside this branch.
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := sorry
