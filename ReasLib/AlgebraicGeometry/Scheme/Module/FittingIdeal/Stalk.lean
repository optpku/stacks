module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk

/-!
# Stalks of Fitting ideal sheaves

The stalk ideal of a Fitting ideal sheaf agrees with the intrinsic Fitting ideal of the
corresponding stalk module.
-/

@[expose] public section

open AlgebraicGeometry
open scoped FittingIdeal

universe u

namespace AlgebraicGeometry.Scheme

/-- The stalk ideal of the `r`th Fitting ideal sheaf is the `r`th Fitting ideal of the stalk
module. -/
@[simp]
theorem fittingIdealSheaf_stalkIdeal_eq_stalk_fittingIdeal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (s : S) (r : ℕ) :
    RingedSpace.idealSheafStalkIdeal (fittingIdealSheaf ℱ r).toSubobject s =
      Fit[S.presheaf.stalk s]_(r)(RingedSpace.stalkModuleCat ℱ s) := sorry

end AlgebraicGeometry.Scheme
