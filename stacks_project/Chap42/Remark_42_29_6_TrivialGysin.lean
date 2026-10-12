/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TrivialRestriction

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
  (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ)

#check (AlgebraicGeometry.Scheme.Modules.trivialGysin p δ ℒ s htriv k :
  CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k)

end AlgebraicGeometry.Scheme.Modules
