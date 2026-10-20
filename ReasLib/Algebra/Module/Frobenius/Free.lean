module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.Module
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.RingTheory.FittingIdeal.Basic
public import ReasLib.RingTheory.FittingIdeal.LocallyFree

@[expose] public section

open CategoryTheory

universe u v

namespace Module

/-- A finite module over a Noetherian local ring in which a prime vanishes is free
if scalar extension along the prime-power Frobenius endomorphism is isomorphic to itself. -/
theorem free_of_frobeniusBaseChange_iso
    (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hp : (p : A) = 0) (M : ModuleCat.{max u v} A)
    [Module.Finite A M]
    (h_frobenius :
      Nonempty ((ModuleCat.extendScalars (RingHom.frobeniusOfPrime p hp)).obj M ≅ M)) :
    Module.Free A M := sorry

end Module
