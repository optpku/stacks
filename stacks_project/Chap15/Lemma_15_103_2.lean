/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor.Vanishing

/-!
# Lemma 15.103.2

@stack 0FXN
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.IdealPower
open CategoryTheory.DerivedCategory.IdealPower.Tor

universe u

/- Lemma 15.103.2 (0FXN): if `M` is finite over a Noetherian ring and `I` annihilates `N`,
then a positive ideal-power stage induces the zero map on every `Tor_p(-, N)`. -/
@[stacks 0FXN "Lemma 15.103.2"]
#check @UniformZero.of_annihilator

#check fun {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) ↦
  (show ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ, subtypeTorMap I M N n p = 0 from
    UniformZero.of_annihilator I M N hN)

#check @UniformZero
#check @EventuallyZero
#check @subtypeTorMap
#check @UniformZero.eventuallyZero
