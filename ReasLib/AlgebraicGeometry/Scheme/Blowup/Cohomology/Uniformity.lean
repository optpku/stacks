module

public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- Positive-degree cohomology of every sufficiently positive thickened twist vanishes. -/
theorem thickenedTwistCohomology_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (n q i : ℕ) (hn : 0 < n) (hq : q₀ ≤ q) (hi : 0 < i) :
    IsZero (Scheme.Hom.cohomology p
      (thickenedTwistingSheaf I p n (q : ℤ)) i) := sorry

/-- Global sections of every sufficiently positive thickened twist are the corresponding ideal-power quotient. -/
theorem thickenedTwistCohomology_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (hSections : ∀ {r : ℕ}, q₀ ≤ r →
      IsIsomorphic
        (Scheme.Hom.cohomology p
          (thickenedTwistingSheaf I p 1 (r : ℤ)) 0)
        (Ideal.PowerQuotient.stage I (ModuleCat.of A (I ^ r : Ideal A)) 1))
    (n q : ℕ) (hn : 0 < n) (hq : q₀ ≤ q) :
    IsIsomorphic
      (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p n (q : ℤ)) 0)
      (Ideal.PowerQuotient.stage I (ModuleCat.of A (I ^ q : Ideal A)) n) := sorry

/-- Positive-degree cohomology of every sufficiently positive unthickened twist vanishes. -/
theorem twistCohomology_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (q i : ℕ) (hq : q₀ ≤ q) (hi : 0 < i) :
    IsZero (Scheme.Hom.cohomology p (twistingSheaf I p (q : ℤ)) i) := sorry

/-- Global sections of every sufficiently positive unthickened twist are the corresponding ideal power. -/
theorem twistCohomology_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (hSections : ∀ {r : ℕ}, q₀ ≤ r →
      IsIsomorphic
        (Scheme.Hom.cohomology p
          (thickenedTwistingSheaf I p 1 (r : ℤ)) 0)
        (Ideal.PowerQuotient.stage I (ModuleCat.of A (I ^ r : Ideal A)) 1))
    (q : ℕ) (hq : q₀ ≤ q) :
    IsIsomorphic
      (Scheme.Hom.cohomology p (twistingSheaf I p (q : ℤ)) 0)
      (ModuleCat.of A (I ^ q : Ideal A)) := sorry

end AlgebraicGeometry.IsBlowup
