module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Characterization

@[expose] public section

/-!
# Normalizations over Nagata Rings

This leaf records finiteness of the relative integral closure in reduced
essentially finite-type Nagata algebras.
-/

universe u v

namespace NagataRing

/-- Lemma 10.162.2, tag `03GH`: the integral closure of a Nagata ring in a
reduced algebra essentially of finite type is finite over the base. -/
@[stacks 03GH]
theorem moduleFinite_integralClosure_of_essFiniteType_of_isReduced
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [NagataRing R] [Algebra.EssFiniteType R S] [IsReduced S] :
    Module.Finite R (integralClosure R S) := sorry

end NagataRing
