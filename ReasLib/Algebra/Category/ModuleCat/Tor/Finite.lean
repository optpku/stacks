/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution

/-!
# Finiteness of `Tor`

This leaf records the Noetherian finiteness theorem for the derived `Tor`
bifunctor. The statement is an ordinary theorem rather than a global
instance, so callers retain control over the finiteness evidence used in a
proof.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 10.75.7, tag `0AZ4`: every `Tor` degree of finite modules over a
Noetherian ring is finite. -/
@[stacks 0AZ4 "finiteness of Tor"]
theorem finite (M N : ModuleCat R) [Module.Finite R M] [Module.Finite R N] (p : ℕ) :
    Module.Finite R (((CategoryTheory.Tor (ModuleCat R) p).obj M).obj N) := sorry

end CategoryTheory.ModuleCat.Tor
