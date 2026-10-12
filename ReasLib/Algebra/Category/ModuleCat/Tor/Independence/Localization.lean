/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor independence and localization

Tor independence of two commutative algebras can be tested either at compatible prime
localizations of the algebras or by localizing their positive Tor modules over the tensor-product
algebra.

@stack 08HX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CategoryTheory.ModuleCat.Tor.IsIndependent

/-- Lemma 15.61.6, Stacks `08HX`: Tor independence of two commutative algebras is equivalent both
to Tor independence at every compatible triple of prime localizations and to vanishing of every
positive Tor module after localization at each prime of the tensor-product algebra. -/
@[stacks 08HX "Tor independence is local on compatible primes"]
theorem tfae_localization
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    List.TFAE
      [ IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)
      , ∀ r : PrimeSpectrum R,
          ∀ p : r.asIdeal.primesOver A,
            ∀ q : r.asIdeal.primesOver B,
              -- Local instance justification (instance diamond): orient the localization map
              -- from the common base prime to the chosen prime of `A`.
              letI : Algebra (Localization.AtPrime r.asIdeal)
                  (Localization.AtPrime p.1) :=
                Localization.AtPrime.algebraOfLiesOver r.asIdeal p.1
              -- Local instance justification (instance diamond): orient the localization map
              -- from the common base prime to the chosen prime of `B`.
              letI : Algebra (Localization.AtPrime r.asIdeal)
                  (Localization.AtPrime q.1) :=
                Localization.AtPrime.algebraOfLiesOver r.asIdeal q.1
              IsIndependent
                (ModuleCat.of (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.1))
                (ModuleCat.of (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.1))
      , ∀ s : PrimeSpectrum (A ⊗[R] B),
          ∀ i : ℕ, 0 < i →
            IsZero
              (ModuleCat.of (Localization.AtPrime s.asIdeal)
                (LocalizedModule.AtPrime s.asIdeal
                  (ModuleCat.Tor.TensorAction.obj (R := R) (A := A) (B := B) i)))
      ] := sorry

end CategoryTheory.ModuleCat.Tor.IsIndependent
