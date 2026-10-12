/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.UniversallyInjective
import StacksCheckRecall

@[expose] public section

universe u

/- Theorem 35.4.22: descent for modules, effective descent for modules, and universal
injectivity are equivalent for a morphism of commutative rings. -/
@[stacks 08XA] #check (RingHom.tfae_descentForModules :
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    List.TFAE [(algebraMap R S).DescentForModules,
      (algebraMap R S).EffectiveDescentForModules,
      LinearMap.UniversallyInjective (Algebra.linearMap R S)])
