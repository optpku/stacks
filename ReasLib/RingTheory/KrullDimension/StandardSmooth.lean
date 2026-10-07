module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fiber Dimension of Submersive Presentations

This leaf records the dimension of a nonempty fiber of a submersive
presentation.  The statement is intrinsic to the presentation and does not
depend on a choice of finite indexing equivalence.
-/

universe u v w x

namespace Algebra.SubmersivePresentation

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.137.6 (5), tag `00T7`: every nonempty fiber of a submersive
presentation has Krull dimension equal to its presentation dimension. -/
@[stacks 00T7 "fiber dimension of a submersive presentation"]
theorem fiber_ringKrullDim_eq_dimension
    [Finite ι] [Finite σ] (P : SubmersivePresentation R S ι σ) (p : PrimeSpectrum R)
    (hp : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S))) :
    ringKrullDim (p.asIdeal.Fiber S) = P.dimension := sorry

end Algebra.SubmersivePresentation
