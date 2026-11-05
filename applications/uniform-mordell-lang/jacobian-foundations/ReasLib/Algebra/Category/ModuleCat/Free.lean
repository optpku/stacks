module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Standard finite-rank free modules

This file names the universe-correct free module of rank `n`.  Downstream statements can use the
mathematical rank while the owner hides the `ULift (Fin n)` implementation detail.
-/

@[expose] public section

universe u

namespace ModuleCat

/-- The standard free `R`-module of rank `n`, with its basis lifted to the universe of `R`. -/
noncomputable abbrev freeFin (R : Type u) [Ring R] (n : ℕ) : ModuleCat R :=
  (free R).obj (ULift.{u} (Fin n))

end ModuleCat
