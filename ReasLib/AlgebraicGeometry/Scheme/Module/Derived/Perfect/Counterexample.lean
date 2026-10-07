module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- There exists a scheme with a perfect derived `𝒪_X`-module that has no globally
bounded, termwise locally free complex representative. -/
theorem existsPerfectWithoutGlobalLocallyFreeModel :
    ∃ (X : Scheme.{u}) (K : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect K ∧
        ¬ ∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
          IsIsomorphic (DerivedCategory.Q.obj P) K ∧
            CochainComplex.bounded X.toRingedSpace.Modules P ∧
              ∀ i : ℤ, (P.X i).IsLocallyFree := sorry

end AlgebraicGeometry.Scheme
