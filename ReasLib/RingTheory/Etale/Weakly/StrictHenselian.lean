module

public import ReasLib.RingTheory.Algebra.IsEpi
public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.Henselian.StrictHenselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly etale algebras over strictly henselian local rings

A local weakly etale algebra over a strictly henselian local ring is already isomorphic to its
base ring.

@stack 092Z
-/

@[expose] public section

universe u v

namespace Algebra.WeaklyEtale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [StrictHenselianLocalRing A] [IsLocalRing B]

/-- A weakly etale local map out of a strictly henselian local ring is a ring epimorphism. -/
@[stacks 092Z "the epimorphism step in Olivier's theorem"]
theorem isEpi_of_isLocalHom_of_strictHenselianLocalRing
    (hlocal : IsLocalHom (algebraMap A B)) (h : Algebra.WeaklyEtale A B) :
    Algebra.IsEpi A B := sorry

/-- Theorem 15.105.24 (Olivier), Stacks `092Z`: a weakly etale local homomorphism from a strictly
henselian local ring to a local ring is bijective. -/
@[stacks 092Z "Olivier's theorem"]
theorem algebraMap_bijective_of_isLocalHom_of_strictHenselianLocalRing
    (hlocal : IsLocalHom (algebraMap A B)) (h : Algebra.WeaklyEtale A B) :
    Function.Bijective (algebraMap A B) := sorry

end Algebra.WeaklyEtale
