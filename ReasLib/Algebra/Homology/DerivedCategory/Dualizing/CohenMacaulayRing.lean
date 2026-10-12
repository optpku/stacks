/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.CohenMacaulayRing
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A finite module concentrated in degree zero that is dualizing forces its
commutative Noetherian ring to be Cohen--Macaulay. -/
theorem cohenMacaulayRingOfSingle
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : ModuleCat.{u} A) [Module.Finite A ω]
    (hω : (ModuleCat.single0 ω).IsDualizingComplex H) :
    CohenMacaulayRing A := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex

end
