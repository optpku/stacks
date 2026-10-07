module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.AdicCompletion.FiniteModule
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import ReasLib.RingTheory.LocalCohomology.Cutoff

@[expose] public section

open IsLocalRing
open scoped ENat

universe u v

namespace Module.LocalCohomology

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [UniversallyCatenaryRing.{u, u} A]
variable (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- For a universally catenary local ring and a finite module, completion at the maximal
ideal cannot increase the local-cohomology finiteness cutoff. -/
theorem cutoff_adicCompletion_le :
    cutoff (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
        (AdicCompletion (maximalIdeal A) M) ≤ cutoff I M := sorry

/-- For a universally catenary local ring whose formal fibers satisfy Serre's condition
`S_n`, the completed cutoff is at least the minimum of `n + 1` and the original cutoff. -/
theorem min_le_cutoff_adicCompletion_of_formalFibers (n : ℕ)
    (h_formal : (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers A) :
    min ((n + 1 : ℕ) : WithBot ℕ∞) (cutoff I M) ≤
      cutoff (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A)))
        (AdicCompletion (maximalIdeal A) M) := sorry

end Module.LocalCohomology
