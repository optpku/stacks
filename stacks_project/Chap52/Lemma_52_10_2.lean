/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap52.Situation_52_10_1
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation

open CategoryTheory

universe u v

/- Lemma 52.10.2: if `p ≤ q`, with `p ∉ V(I)` and `q ∈ T`, and no prime of
`V(I) \ T` lies between them, then the depth of `M` localized at `p` is greater than `s`. -/
@[stacks 0EID] #check
  (@Ideal.LocalCohomology.AlgebraizationSituation.depth_gt_of_no_intermediate :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      {M : Type v} → [AddCommGroup M] → [Module A M] → [Module.Finite A M] →
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      {I : Ideal A} → {T : Set (PrimeSpectrum A)} → {s d : ℤ} →
      Ideal.LocalCohomology.AlgebraizationSituation H I M T s d →
      (p q : PrimeSpectrum A) → p.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) → q ∈ T →
      (¬ ∃ r : PrimeSpectrum A,
        r ∈ PrimeSpectrum.zeroLocus (I : Set A) ∧ r ∉ T ∧
          p.asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ q.asIdeal) →
      (s : EInt) <
        ((WithTop.map Int.ofNat
          (moduleDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt))
