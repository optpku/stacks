module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Retracts
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Summands of pseudo-coherent derived modules on ringed spaces

The ringed-space predicates inherit retract stability from the bundled opens site.  This leaf
provides the direct biproduct interface expected by downstream arguments.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

namespace IsMPseudoCoherent

/-- Lemma 20.47.6 (1,2): both summands of an `m`-pseudo-coherent biproduct are
`m`-pseudo-coherent. -/
@[stacks 08CE "(1,2)"]
theorem summands (K L : ModuleDerived X) {m : ℤ}
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m ∧ IsMPseudoCoherent L m := sorry

/-- Lemma 20.47.6 (1): the left summand is `m`-pseudo-coherent. -/
@[stacks 08CE "(1)"]
theorem left (K L : ModuleDerived X) {m : ℤ}
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m := sorry

/-- Lemma 20.47.6 (2): the right summand is `m`-pseudo-coherent. -/
@[stacks 08CE "(2)"]
theorem right (K L : ModuleDerived X) {m : ℤ}
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent L m := sorry

end IsMPseudoCoherent

namespace IsPseudoCoherent

/-- Lemma 20.47.6 (3,4): both summands of a pseudo-coherent biproduct are pseudo-coherent. -/
@[stacks 08CE "(3,4)"]
theorem summands (K L : ModuleDerived X)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K ∧ IsPseudoCoherent L := sorry

/-- Lemma 20.47.6 (3): the left summand is pseudo-coherent. -/
@[stacks 08CE "(3)"]
theorem left (K L : ModuleDerived X)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K := sorry

/-- Lemma 20.47.6 (4): the right summand is pseudo-coherent. -/
@[stacks 08CE "(4)"]
theorem right (K L : ModuleDerived X)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent L := sorry

end IsPseudoCoherent

end AlgebraicGeometry.RingedSpace.ModuleDerived
