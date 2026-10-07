module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.FiniteLocallyFree

/-!
# Base change of eta complexes with principal determinantal ideals

The eta base-change comparison is defined without hypotheses in `Eta.BaseChange`.  This file
shows that the same canonical morphism is an isomorphism when the relevant determinantal ideals
are principal, without requiring the algebra itself to be flat.
@stack 0F7X
-/

@[expose] public section

open CategoryTheory
open scoped BerthelotOgus nonZeroDivisors

universe u v w

namespace CochainComplex.BerthelotOgus.Nat.BaseChange

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- In one degree, principality of the eta determinantal ideal makes the canonical base-change
map on eta terms bijective. -/
theorem termLinear_bijective_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Function.Bijective (termLinear (B := B) f K i) := sorry

/-- In one degree, the bundled canonical comparison is an isomorphism under the same local
principal-ideal hypotheses. -/
theorem termHom_isIso_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (termHom (B := B) f K i) := sorry

/-- If every eta determinantal ideal is principal, the canonical base-change comparison is an
isomorphism; boundedness is not needed for this strengthened form. -/
theorem comparison_isIso_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (comparison (B := B) f K) := sorry

/-- Lemma 15.97.6, Tag 0F7X: for a bounded finite-free complex with principal eta
determinantal ideals, the canonical eta base-change comparison is an isomorphism. -/
@[stacks 0F7X "base change for the Berthelot-Ogus eta complex"]
theorem comparison_isIso
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ)
    (hK : CochainComplex.Nat.IsBoundedAbove K)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (comparison (B := B) f K) := sorry

end CochainComplex.BerthelotOgus.Nat.BaseChange
