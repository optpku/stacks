/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.Flat
public import ReasLib.RingTheory.RingHom.Perfect.Flat

@[expose] public section

open CategoryTheory
open ModuleCat
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory
namespace ModuleCat
namespace UpperShriek

/-- For a perfect map of Noetherian rings and a Tor-independent base change, the
upper-shriek base-change comparison is an isomorphism. -/
theorem baseChangeComparison_isIso_of_isPerfect
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [(algebraMap R A).IsPerfectRingMap]
    (p : Presentation (algebraMap R A))
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso (p.baseChangeComparison R' hTor) := sorry

/-- For Noetherian rings, the upper-shriek base-change comparison of a flat
finite-type algebra is an isomorphism. -/
theorem baseChangeComparison_isIso_of_flat_finiteType
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Module.Flat R A] [Algebra.FiniteType R A]
    (p : Presentation (algebraMap R A)) :
    IsIso (p.baseChangeComparison R' (Tor.IsIndependent.of_flat_left R')) := sorry

end UpperShriek
end ModuleCat
end CategoryTheory
