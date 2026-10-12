/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
public import ReasLib.Algebra.Homology.LocalCohomology.MittagLeffler

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open SequentialInverseSystem.Milnor.ProductCone

noncomputable section

universe u

namespace CategoryTheory
namespace DerivedCategory
namespace LocalCohomology
namespace Completion

variable {A : Type u} [CommRing A]

/-- The tower whose `n`th stage is the underlying derived object of
`RΓ_Z((M / I ^ (n + 1) M)[0])`. -/
noncomputable abbrev quotientSystem (I J : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{u} A)) :=
  Ideal.PowerQuotient.positiveSystem I M ⋙ ModuleCat.single0Functor ⋙ RΓZ ⋙
    IdealPowerTorsion.inclusion J

/-- The object at stage `n` of `quotientSystem` is local cohomology of
`M / I ^ (n + 1) M`, viewed in the ambient derived category. -/
theorem quotientSystem_obj (I J : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (M : ModuleCat.{u} A) (n : ℕ) :
    (quotientSystem I J RΓZ M).obj (Opposite.op n) =
      (RΓZ.obj (ModuleCat.single0 (Ideal.PowerQuotient.positiveStage I M n))).obj := sorry

/-- Derived completion of local cohomology is a homotopy limit of local cohomology
of the positive ideal-power quotient tower. -/
theorem isHomotopyLimit [IsNoetherianRing A] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (hRΓZ : IdealPowerTorsion.inclusion J ⊣ RΓZ) :
    HomotopyLimit.IsOf (quotientSystem I J RΓZ M)
      (derivedCompletionOf I I.fg_of_isNoetherianRing
        (RΓZ.obj (ModuleCat.single0 M)).obj) := sorry

/-- In every degree, cohomology of the completed local-cohomology object lies in
the Milnor short exact sequence of the positive ideal-power quotient tower. -/
theorem cohomologyShortExact [IsNoetherianRing A] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (hRΓZ : IdealPowerTorsion.inclusion J ⊣ RΓZ) (i : ℤ) :
    ∃ (ι : canonicalR1
          (quotientSystem I J RΓZ M ⋙
            homologyFunctor (ModuleCat.{u} A) (i - 1)) ⟶
          (homologyFunctor (ModuleCat.{u} A) i).obj
            (derivedCompletionOf I I.fg_of_isNoetherianRing
              (RΓZ.obj (ModuleCat.single0 M)).obj))
      (π : (homologyFunctor (ModuleCat.{u} A) i).obj
            (derivedCompletionOf I I.fg_of_isNoetherianRing
              (RΓZ.obj (ModuleCat.single0 M)).obj) ⟶
          limit (quotientSystem I J RΓZ M ⋙
            homologyFunctor (ModuleCat.{u} A) i))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- Derived completion of local cohomology of a finite module is concentrated in
nonnegative cohomological degrees. -/
theorem isGE_zero [IsNoetherianRing A] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (hRΓZ : IdealPowerTorsion.inclusion J ⊣ RΓZ) :
    (derivedCompletionOf I I.fg_of_isNoetherianRing
      (RΓZ.obj (ModuleCat.single0 M)).obj).IsGE 0 := sorry

/-- Negative-degree homology of the completed local-cohomology object is zero. -/
theorem homology_isZero_of_neg [IsNoetherianRing A] (I J : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓZ : DerivedCategory (ModuleCat.{u} A) ⥤ IdealPowerTorsion J)
    (hRΓZ : IdealPowerTorsion.inclusion J ⊣ RΓZ) (i : ℤ) (hi : i < 0) :
    IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
      (derivedCompletionOf I I.fg_of_isNoetherianRing
        (RΓZ.obj (ModuleCat.single0 M)).obj)) := sorry

/-- For a Noetherian local ring, the cohomology of derived completion of local
cohomology of a finite module is the inverse limit of the cohomology of its
positive ideal-power quotient tower. -/
theorem cohomologyIsIsomorphicLimit
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (RΓm : DerivedCategory (ModuleCat.{u} A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓm : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓm)
    (i : ℤ) :
    IsIsomorphic
      ((homologyFunctor (ModuleCat.{u} A) i).obj
        (derivedCompletionOf I I.fg_of_isNoetherianRing
          (RΓm.obj (ModuleCat.single0 M)).obj))
      (limit (quotientSystem I (IsLocalRing.maximalIdeal A) RΓm M ⋙
        homologyFunctor (ModuleCat.{u} A) i)) := sorry

end Completion
end LocalCohomology
end DerivedCategory
end CategoryTheory
