/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Jacobson
import StacksCheckRecall

@[expose] public section

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.16.1: for ideals `I ≤ I'` in a Noetherian ring `A` with
`ringKrullDim A = d`, if `I' ≤ Ring.jacobson A` and the local-cohomological
dimension of `I'` is less than `d`, then the local-cohomological dimension of
`I` is less than `d`. -/
@[stacks 0EB1] #check (Ideal.LocalCohomology.dimension_lt_of_le_of_le_ringJacobson :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (d : ℕ)
    (hdim : ringKrullDim A = d) (I I' : Ideal A) (h_le : I ≤ I')
    (h_jacobson : I' ≤ Ring.jacobson A)
    (h_cd : Ideal.LocalCohomology.dimension I' I'.fg_of_isNoetherianRing < (d : ℤ)),
    Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing < (d : ℤ))

end Ideal.LocalCohomology
