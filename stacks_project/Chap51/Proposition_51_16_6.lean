/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaum
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u

namespace Ideal.LocalCohomology

/- Proposition 51.16.6: if every top-dimensional minimal component of the
maximal-ideal completion of a Noetherian local ring meets the zero locus of an
ideal in dimension at least one, then the ideal's local-cohomological dimension
is strictly less than the dimension of the ring. -/
@[stacks 0EB6] #check
  (Ideal.LocalCohomology.dimension_lt_ringKrullDim_of_completion_components :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (I : Ideal A)
      (h_dimension : let Ahat := AdicCompletion (maximalIdeal A) A
        ∀ p ∈ minimalPrimes.topDim Ahat,
          1 ≤ ringKrullDim (Ahat ⧸ (I.map (algebraMap A Ahat) ⊔ p))),
      (dimension I I.fg_of_isNoetherianRing : EInt) <
        WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A))

end Ideal.LocalCohomology
