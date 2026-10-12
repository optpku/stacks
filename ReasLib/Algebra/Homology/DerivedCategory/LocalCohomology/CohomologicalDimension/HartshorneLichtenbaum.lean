/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.KrullDimension
public import ReasLib.RingTheory.Completion.Dimension
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Ideal.MinimalPrime.TopDimension
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

open IsLocalRing

universe u

namespace Ideal.LocalCohomology

/-- If every top-dimensional minimal component of the maximal-ideal completion of a
Noetherian local ring meets the zero locus of an ideal in dimension at least one,
then the ideal's local-cohomological dimension is strictly less than the Krull
dimension of the ring. -/
theorem dimension_lt_ringKrullDim_of_completion_components
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A)
    (h_dimension : let Ahat := AdicCompletion (maximalIdeal A) A
      ∀ p ∈ minimalPrimes.topDim Ahat,
        1 ≤ ringKrullDim (Ahat ⧸ (I.map (algebraMap A Ahat) ⊔ p))) :
    (dimension I I.fg_of_isNoetherianRing : EInt) <
      WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A) := sorry

/-- If an ideal in an excellent normal local ring has quotient of Krull
dimension at least one, its local-cohomological dimension is strictly less
than the Krull dimension of the ring. -/
@[stacks 0EB7]
theorem dimension_lt_ringKrullDim_of_excellent_normal
    {A : Type u} [CommRing A] [IsLocalRing A] [IsExcellentRing.{u, u} A]
    [IsNormalRing A] (I : Ideal A) (h_dimension : 1 ≤ ringKrullDim (A ⧸ I)) :
    (dimension I I.fg_of_isNoetherianRing : EInt) <
      WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A) := sorry

end Ideal.LocalCohomology
