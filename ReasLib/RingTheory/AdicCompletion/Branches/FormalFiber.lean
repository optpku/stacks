/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches
public import ReasLib.RingTheory.Normal.Nagata.GeometricallyNormalFormalFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch numbers and geometrically normal formal fibers

For a Noetherian local ring with geometrically normal formal fibers, ordinary and geometric branch
numbers are preserved by maximal-ideal completion.

@stack 0C2E
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

namespace BranchNumber

/-- Lemma 15.109.8 (2): if a Noetherian local ring has geometrically normal formal fibers, its
branch number equals the number of minimal primes of its maximal-ideal completion. -/
@[stacks 0C2E "Lemma 15.109.8 (2)"]
theorem eq_completion_minimalPrimes_of_geometricallyNormalFormalFibers
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) :
    branchNumber A Ah =
      (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard := sorry
-- Proof strategy: geometric normality makes the radical of every extended henselization
-- minimal prime prime; apply
-- `branchNumber_eq_minimalPrimes_iff_radical_map_isPrime` to the canonical comparison.

end BranchNumber

namespace GeometricBranchNumber

/-- Lemma 15.109.8 (3): if a Noetherian local ring has geometrically normal formal fibers, its
geometric branch number is preserved by maximal-ideal completion. -/
@[stacks 0C2E "Lemma 15.109.8 (3)"]
theorem eq_completion_of_geometricallyNormalFormalFibers
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ash : Type v} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    {Ahatsh : Type w} [CommRing Ahatsh]
    [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
    [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]
    (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) :
    geometricBranchNumber A Ash =
      geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh := sorry
-- Proof strategy: apply the ordinary branch equality to the strict henselizations; geometric
-- normality of formal fibers is preserved by the required residue-field base changes.

end GeometricBranchNumber
