module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Composition
public import ReasLib.RingTheory.RingHom.Syntomic.Localization

@[expose] public section

/-!
# Composition of Syntomic Ring Homomorphisms

This leaf owns composition and the corresponding generic stability witness for
the intrinsic `RingHom.Syntomic` predicate.
-/

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']

namespace Syntomic

/-- Lemma 10.136.17 (1): the composite of syntomic ring homomorphisms is
syntomic. -/
@[stacks 00SZ "composition of syntomic ring homomorphisms"]
theorem comp {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic) :
    (g.comp f).Syntomic := sorry

/-- Lemma 10.136.17 (1): syntomic ring homomorphisms form a property stable
under composition. -/
@[stacks 00SZ "syntomic stability under composition"]
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.Syntomic := sorry

end Syntomic

end RingHom
