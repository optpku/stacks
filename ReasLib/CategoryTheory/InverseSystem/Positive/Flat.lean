/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat.Limits
public import ReasLib.RingTheory.Flatness.Tor

/-!
# Flat limits of positive module inverse systems

This leaf records the tensor comparison and flatness theorem for a surjective inverse system whose
positive stage `Mₙ` is flat over `A ⧸ I ^ n`.

@stack 0912
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.PNatInverseSystem

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M_ : PNatInverseSystem (ModuleCat A))
variable [∀ n : ℕ+, Module (A ⧸ I ^ (n : ℕ)) (M_.stage n)]
variable [∀ n : ℕ+, IsScalarTower A (A ⧸ I ^ (n : ℕ)) (M_.stage n)]

/-- Lemma 15.27.4 (1): for a surjective positive inverse system whose stage `Mₙ` is flat over
`A ⧸ I ^ n`, tensoring the limit with a finite module agrees with the limit of the stagewise
tensors. -/
@[stacks 0912 "Lemma 15.27.4 (1)"]
theorem tensorLimitComparison_bijective
    (hflat : ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.stage n))
    (hsurj : ∀ n : ℕ+, Function.Surjective (M_.stepMap n))
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Bijective (limit.post M_ (tensorLeft (ModuleCat.of A Q))) := sorry

/-- Lemma 15.27.4 (2): a surjective positive inverse system whose stage `Mₙ` is flat over
`A ⧸ I ^ n` has a flat inverse limit over `A`. -/
@[stacks 0912 "Lemma 15.27.4 (2)"]
theorem limit_flat
    (hflat : ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.stage n))
    (hsurj : ∀ n : ℕ+, Function.Surjective (M_.stepMap n)) :
    Module.Flat A (limit M_ : ModuleCat A) := sorry

end CategoryTheory.PNatInverseSystem
