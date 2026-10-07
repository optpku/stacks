module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Surjective
public import ReasLib.RingTheory.CompleteIntersection.Basic
import StacksCheckRecall

/-!
# Regular-sequence kernels along local surjections

@stack 00SE

The kernel predicate is owned by `RingHom.KernelIsGeneratedByRegularSequence`.
This file retains the source's four-way comparison as a thin TFAE bridge; the
dimension and parameter arguments are deliberately left as proposition-valued
clauses rather than reintroducing the proof-specific induction infrastructure.
-/

@[expose] public section

universe u v w

open IsLocalRing

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsRegularLocalRing A] [IsRegularLocalRing B] [IsLocalRing C]

#check @RingHom.KernelIsGeneratedByRegularSequence
#check @Ideal.IsGeneratedByRegularSequence
#check @RingHom.quotientKerEquivOfSurjective

/- Lemma 10.135.6. The four source clauses are a presentation-oriented TFAE view of the kernel
predicates above, so they remain an anonymous contract rather than a second public API. -/
@[stacks 00SE]
#check (show
  ∀ (φ : A →+* B) (ψ : B →+* C) [hφlocal : IsLocalHom φ]
      [hψlocal : IsLocalHom ψ],
    Function.Surjective φ → Function.Surjective ψ →
    List.TFAE
      [ (ψ.comp φ).KernelIsGeneratedByRegularSequence
      , ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim A) (x : Fin d → A),
          Ideal.span (Set.range x) = RingHom.ker (ψ.comp φ)
      , ψ.KernelIsGeneratedByRegularSequence
      , ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim B) (y : Fin d → B),
          Ideal.span (Set.range y) = RingHom.ker ψ
      ] from by sorry)

end

end
