module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogPole.Boundary
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogPole

/-- The first relative de Rham Chern class of the positive line of an effective Cartier divisor. -/
noncomputable def poleLineFirstChernClass {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsEffectiveCartierDivisor i] : cohomology f 2 :=
  @firstChernClass _ _ f (RingedSpace.DeRham.LogPole.poleLine i)
    (@SheafOfModules.RingedSite.dual.isInvertible
      _ _ _ _ _ _ _ (RingedSpace.Hom.idealSheaf i.toShHom) inferInstance inferInstance)

/-- Restriction of relative de Rham cohomology to a subscheme, viewed over the ambient
coefficient ring. -/
def restrictionOnCohomology {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) (m : ℤ) :
    cohomology f m ⟶ Cohomology.restricted (schemeSquare f i) m :=
  Cohomology.restrictedPullback (schemeSquare f i) m
    (hPull := CanonicalTensor.coefficientPushforward_hasRightDerived (schemeSquare f i))

/-- The first de Rham Chern class of a positive effective Cartier divisor annihilates every
class restricting to zero on the divisor when logarithmic de Rham poles are defined. -/
theorem firstChernClass_cup_eq_zero_of_restrict
    {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
    (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) (m : ℤ) (b : cohomology f m)
    (h_restrict : (restrictionOnCohomology f i m).hom b = 0) :
    (eqToHom (congrArg (cohomology f) (add_comm 2 m))).hom
      (CanonicalAction.cup f 2 m
        (poleLineFirstChernClass f i) b) = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham.LogPole
