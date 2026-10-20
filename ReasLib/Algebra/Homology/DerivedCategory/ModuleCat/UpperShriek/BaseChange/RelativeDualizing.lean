module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange.Perfect

@[expose] public section

open CategoryTheory
open ModuleCat
open UpperShriek
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

/-- The degree-zero relative dualizing base-change component is invertible
    for a flat coefficient extension. -/
theorem relativeDualizingBaseChange_isIso_of_baseFlat
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra.FiniteType R A] [Module.Flat R R']
    (p : Presentation (algebraMap R A)) :
    IsIso ((p.flatBaseChange R').app (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- The degree-zero relative dualizing base-change component is invertible
    when the algebra is flat over the base ring. -/
theorem relativeDualizingBaseChange_isIso_of_algebraFlat
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra.FiniteType R A] [Module.Flat R A]
    (p : Presentation (algebraMap R A)) :
    IsIso ((p.baseChangeComparison R' (Tor.IsIndependent.of_flat_left R')).app
      (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- The degree-zero relative dualizing base-change component is invertible for
    a perfect algebra map with Tor-independent coefficient extension. -/
theorem relativeDualizingBaseChange_isIso_of_isPerfect
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Algebra.FiniteType R A] [(algebraMap R A).IsPerfectRingMap]
    (p : Presentation (algebraMap R A))
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso ((p.baseChangeComparison R' hTor).app
      (ModuleCat.single0 (ModuleCat.of R R))) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
