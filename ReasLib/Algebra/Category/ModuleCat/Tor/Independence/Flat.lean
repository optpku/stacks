/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence

@[expose] public section

universe u

namespace CategoryTheory.ModuleCat.Tor.IsIndependent

/-- A flat right coefficient algebra is Tor independent of every algebra over the base ring. -/
theorem of_flat_right {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R R'] :
    Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R') := sorry

/-- A flat left coefficient algebra is Tor independent of every algebra over the base ring. -/
theorem of_flat_left {R A : Type u} (R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] :
    Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R') := sorry

end CategoryTheory.ModuleCat.Tor.IsIndependent
