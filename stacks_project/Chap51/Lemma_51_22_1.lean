/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.Uniformity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 51.22.1 (1): positive cohomology of every positive thickening vanishes
above the exceptional-divisor cutoff. -/
@[stacks 0GA7]
#check (AlgebraicGeometry.IsBlowup.thickenedTwistCohomology_isZero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (n q i : ℕ) (hn : 0 < n) (hq : q₀ ≤ q) (hi : 0 < i),
    IsZero (Scheme.Hom.cohomology p
      (thickenedTwistingSheaf I p n (q : ℤ)) i))

/- Lemma 51.22.1 (2): global sections of every positive thickening are the
corresponding ideal-power quotient above the exceptional-divisor cutoff. -/
@[stacks 0GA7]
#check (AlgebraicGeometry.IsBlowup.thickenedTwistCohomology_zero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
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
    (n q : ℕ) (hn : 0 < n) (hq : q₀ ≤ q),
    IsIsomorphic
      (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p n (q : ℤ)) 0)
      (Ideal.PowerQuotient.stage I (ModuleCat.of A (I ^ q : Ideal A)) n))

/- Lemma 51.22.1 (3): positive cohomology of the unthickened twist vanishes
above the exceptional-divisor cutoff. -/
@[stacks 0GA7]
#check (AlgebraicGeometry.IsBlowup.twistCohomology_isZero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (q₀ : ℕ)
    (hVanishing : ∀ {r j : ℕ}, q₀ ≤ r → 0 < j →
      IsZero (Scheme.Hom.cohomology p
        (thickenedTwistingSheaf I p 1 (r : ℤ)) j))
    (q i : ℕ) (hq : q₀ ≤ q) (hi : 0 < i),
    IsZero (Scheme.Hom.cohomology p (twistingSheaf I p (q : ℤ)) i))

/- Lemma 51.22.1 (4): global sections of the unthickened twist are the
corresponding ideal power above the exceptional-divisor cutoff. -/
@[stacks 0GA7]
#check (AlgebraicGeometry.IsBlowup.twistCohomology_zero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
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
    (q : ℕ) (hq : q₀ ≤ q),
    IsIsomorphic
      (Scheme.Hom.cohomology p (twistingSheaf I p (q : ℤ)) 0)
      (ModuleCat.of A (I ^ q : Ideal A)))

end AlgebraicGeometry.IsBlowup
