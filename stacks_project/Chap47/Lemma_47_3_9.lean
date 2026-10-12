/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Torsion
import StacksCheckRecall

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I]

/- Lemma 47.3.9 (1): The submodule of an injective module consisting of the elements
annihilated by some power of `f` is injective. -/
@[stacks 08XW] #check
  (Module.Injective.fPowerTorsion R I :
    ∀ f : R, Module.Injective R (Submodule.torsion' R I (Submonoid.powers f)))

/- Lemma 47.3.9 (2): The `J`-power torsion submodule of an injective module is
injective. -/
@[stacks 08XW] #check
  (Module.Injective.primaryComponent R I :
    ∀ J : Ideal R, Module.Injective R (J.primaryComponent I))
