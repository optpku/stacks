module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RationalSingularity.SpecialFiberIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 54.9.3 (1): if the special fibre of a normal modification of a rational
surface singularity is an effective Cartier divisor with ideal sheaf `𝓘`, then the
global sections of `𝓘 ^ n`, viewed inside `Γ(X, ⊤)`, are the image of `𝔪 ^ n`. -/
@[stacks 0B4Y] #check
(IsRationalSingularity.specialFiberIdealPower_globalSections :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) (n : ℕ)
    [IsEffectiveCartierDivisor
      ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)).comap f).subschemeι],
    RingedSpace.Modules.subobjectSectionsSubmodule
        (((Scheme.idealSheafDataOfIdealOnSpec
          (IsLocalRing.maximalIdeal A)).comap f) ^ n).toSubobject (⊤ : X.Opens) =
      Ideal.map (Scheme.Hom.globalSectionsMap f) (IsLocalRing.maximalIdeal A ^ n))

/- Lemma 54.9.3 (2): under the same hypotheses, the first cohomology of every power
of the ideal sheaf of the special fibre vanishes. -/
@[stacks 0B4Y] #check
(IsRationalSingularity.specialFiberIdealPower_firstCohomology_isZero :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f]
    (hX : X.isNormal) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) (n : ℕ)
    [IsEffectiveCartierDivisor
      ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)).comap f).subschemeι],
    IsZero (Scheme.Modules.cohomology
      (((Scheme.idealSheafDataOfIdealOnSpec
        (IsLocalRing.maximalIdeal A)).comap f) ^ n).toModule 1))
