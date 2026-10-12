/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.RationalSingularity.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Subobject
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace IsRationalSingularity

/-- If the special fibre of a normal modification of a rational surface singularity
is an effective Cartier divisor with ideal sheaf `𝓘`, then the global sections of
`𝓘 ^ n`, viewed inside `Γ(X, ⊤)`, are the image of the maximal-ideal power `𝔪 ^ n`. -/
theorem specialFiberIdealPower_globalSections
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) (n : ℕ)
    [IsEffectiveCartierDivisor
      ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)).comap f).subschemeι] :
    RingedSpace.Modules.subobjectSectionsSubmodule
        (((Scheme.idealSheafDataOfIdealOnSpec
          (IsLocalRing.maximalIdeal A)).comap f) ^ n).toSubobject (⊤ : X.Opens) =
      Ideal.map (Scheme.Hom.globalSectionsMap f) (IsLocalRing.maximalIdeal A ^ n) := sorry

/-- If the special fibre of a normal modification of a rational surface singularity
is an effective Cartier divisor, then the first cohomology of every power of its
ideal sheaf vanishes. -/
theorem specialFiberIdealPower_firstCohomology_isZero
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) (n : ℕ)
    [IsEffectiveCartierDivisor
      ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)).comap f).subschemeι] :
    IsZero (Scheme.Modules.cohomology
      (((Scheme.idealSheafDataOfIdealOnSpec
        (IsLocalRing.maximalIdeal A)).comap f) ^ n).toModule 1) := sorry

end IsRationalSingularity
