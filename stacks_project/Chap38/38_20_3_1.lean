module

public import ReasLib.RingTheory.Flat.Locus.Closed
import Mathlib.RingTheory.TensorProduct.Basic
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w x

variable {A : Type u} {B : Type v} {A' : Type w} {M : Type x}
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [CommRing A'] [IsLocalRing A']
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra A A'] [IsLocalHom (algebraMap A A')]
variable [AddCommGroup M] [Module B M]

-- Local instance justification (instance diamond): select the right-factor algebra structure on B ⊗[A] A'.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- 38.20.3.1 (05ML): primewise flatness on
`V(𝔪_A'.map (algebraMap A' (B ⊗[A] A')) + 𝔪_B.map (algebraMap B (B ⊗[A] A')))`. -/
@[stacks 05ML]
#check
  (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := A') (S := B ⊗[A] A') (M := (B ⊗[A] A') ⊗[B] M)
      ((IsLocalRing.maximalIdeal A').map (algebraMap A' (B ⊗[A] A')) +
        (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[A] A'))) :
    PrimeSpectrum.zeroLocus
          (((IsLocalRing.maximalIdeal A').map (algebraMap A' (B ⊗[A] A')) +
            (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[A] A'))) :
              Set (B ⊗[A] A')) ⊆
        Module.flatOverBaseLocus A' (B ⊗[A] A') ((B ⊗[A] A') ⊗[B] M) ↔
      ∀ q : PrimeSpectrum (B ⊗[A] A'),
        q ∈ PrimeSpectrum.zeroLocus
          (((IsLocalRing.maximalIdeal A').map (algebraMap A' (B ⊗[A] A')) +
            (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[A] A'))) :
              Set (B ⊗[A] A')) →
          Module.Flat A'
            (LocalizedModule.AtPrime q.asIdeal ((B ⊗[A] A') ⊗[B] M)))
