/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory
open scoped ModuleTor

universe u

namespace CategoryTheory.ModuleCat.Tor

/-- If `t` bounds the number of generators of an ideal `I` in a Noetherian ring `A`,
then one power of `I` annihilates `Tor⁽i⁾[A](M, (A ⧸ (I ^ q)))` uniformly over
all `A`-modules `M`, all degrees `i > t`, and all exponents `q : ℕ`. -/
theorem exists_pow_le_annihilator_tor_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (t : ℕ)
    (h_generators : ∃ a : Fin t → I,
      I = Ideal.span (Set.range fun j ↦ (a j : A))) :
    ∃ c : ℕ, ∀ (M : ModuleCat.{u} A) (i q : ℕ), t < i →
      I ^ c ≤ Module.annihilator A Tor⁽i⁾[A](M, (A ⧸ (I ^ q))) := sorry

end CategoryTheory.ModuleCat.Tor
