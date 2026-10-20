/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor towers of positive ideal-power quotients

Applying `Tor_p^A(M, -)` to the positive ideal-power quotient system gives the
canonical tower whose stage `n` is `Tor_p^A(M, A / I^(n+1))`.

@stack 0EET
@stack 0911
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

variable {A : Type u} [CommRing A]

/-- The sequential inverse system with stage `n` equal to
`Tor_p^A(M, A / I^(n+1))`. -/
@[stacks 0EET "positive ideal-power Tor system"]
abbrev torSystem (I : Ideal A) (M : ModuleCat A) (p : ℕ) :
    SequentialInverseSystem (ModuleCat A) :=
  Ideal.PowerQuotient.positiveSystem I (ModuleCat.of A A) ⋙
    (Tor (ModuleCat A) p).obj M

/-- The object at stage `n` of the positive ideal-power Tor system. -/
@[simp, stacks 0EET "positive ideal-power Tor stage"]
theorem torSystem_obj (I : Ideal A) (M : ModuleCat A) (p n : ℕ) :
    (torSystem I M p).obj (op n) =
      ((Tor (ModuleCat A) p).obj M).obj
        (Ideal.PowerQuotient.positiveStage I (ModuleCat.of A A) n) := sorry

/-- The successor transition in the positive ideal-power Tor system is the
map induced by the corresponding quotient transition. -/
@[simp, stacks 0EET "positive ideal-power Tor transition"]
theorem torSystem_stepMap (I : Ideal A) (M : ModuleCat A) (p n : ℕ) :
    (torSystem I M p).stepMap n =
      ((Tor (ModuleCat A) p).obj M).map
        (Ideal.PowerQuotient.positiveStep I (ModuleCat.of A A) n) := sorry

/-- For a finite module in positive Tor degree over a Noetherian ring,
one positive offset makes every sufficiently deep map
`Tor_p^A(M, A / I^n) ⟶ Tor_p^A(M, A / I^(n-c))` zero. -/
@[stacks 0911]
theorem torPowerMap_eq_zero_eventually
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat A) [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      ((Tor (ModuleCat A) p).obj M).map
          (ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))) = 0 := sorry

/-- The positive ideal-power Tor tower is eventually zero in every positive
Tor degree for a finite module over a Noetherian ring. -/
@[stacks 0911 "positive Tor tower is pro-zero"]
theorem torSystem_transitionMap_eq_zero_eventually
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat A) [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      (torSystem I M p).transitionMap (Nat.sub_le n c) = 0 := sorry

/-- Over a Noetherian ring, each fixed power-annihilation bound and positive Tor
degree admit a uniform cutoff for ideal-power quotient transition maps on Tor,
valid for every module annihilated by that power of the ideal. -/
@[stacks 0G9X]
theorem torPowerMap_eq_zero_uniformly_of_pow_le_annihilator
    [IsNoetherianRing A] (I : Ideal A) (m i : ℕ) (hi : 0 < i) :
    ∃ c : ℕ, ∀ M : ModuleCat.{u} A, I ^ m ≤ Module.annihilator A M →
      ∀ n : ℕ, c ≤ n →
        ((Tor (ModuleCat.{u} A) i).obj M).map
          (ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))) = 0 := sorry

/-- For an ideal with at most `t` generators in a Noetherian ring, sufficiently
deep transition maps in Tor degree `t + 1` vanish uniformly for every module. -/
theorem torPowerMap_eq_zero_uniformly_of_generator_bound
    [IsNoetherianRing A] (I : Ideal A) (t : ℕ)
    (h_generators : ∃ a : Fin t → I,
      I = Ideal.span (Set.range fun j ↦ (a j : A))) :
    ∃ N c : ℕ, ∀ (M : ModuleCat.{u} A) (n : ℕ), N ≤ n →
      ((Tor (ModuleCat.{u} A) (t + 1)).obj M).map
        (ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))) = 0 := sorry

end CategoryTheory.DerivedCategory.IdealPower
