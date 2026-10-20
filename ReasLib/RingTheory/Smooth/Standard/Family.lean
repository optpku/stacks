module

public import ReasLib.RingTheory.Smooth.Standard.Linear

/-!
# Finite families in standard-smooth presentations

This leaf records the coordinate-free statement that a finite family can be
included among the distinguished variables of a submersive presentation.
Coordinate normalization belongs in `Standard.Normalized`.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite family in a standard-smooth algebra can be included among the
distinguished variables of a finite submersive presentation. -/
@[stacks 07EY "finite families in standard-smooth presentations"]
theorem IsStandardSmooth.exists_presentation_containing
    {κ : Type w} [Finite κ] [IsStandardSmooth R A] (β : κ → A) :
    ∃ (ι σ : Type w) (_ : Finite ι) (_ : Finite σ)
      (P : SubmersivePresentation R A ι σ) (j : κ ↪ σ),
      ∀ k, P.val (P.map (j k)) = β k := sorry

end Algebra
