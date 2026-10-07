module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.FiniteLocallyFree

/-!
# Principal-ideal base change for integer-indexed eta complexes

The comparison map is the one defined in `Eta.Int.BaseChange`.  Principality of the
degreewise eta determinantal ideals makes it an isomorphism without assuming that the algebra
is flat.
@stack 0F7X
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Int.BaseChange

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Scalar extension preserves the termwise finite-free class of an integer-indexed complex. -/
@[stacks 0F7X "finite-free scalar extension for integer-indexed complexes"]
instance scalarExtension_isTermwiseFiniteFree
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ) [K.IsTermwiseFiniteFree] :
    ((scalarExtension (A := A) (B := B)).obj K).IsTermwiseFiniteFree := sorry

/-- A nonzerodivisor acts regularly on the scalar extension of a termwise finite-free
integer-indexed complex. -/
@[stacks 0F7X "regularity of the scalar-extended finite-free complex"]
theorem scalarExtension_isTermwiseTorsionFree
    (K : CochainComplex (ModuleCat.{max v w} A) ℤ) [K.IsTermwiseFiniteFree]
    {g : B} (hg : g ∈ nonZeroDivisors B) :
    IsTermwiseTorsionFree g ((scalarExtension (A := A) (B := B)).obj K) := sorry

/-- The canonical integer eta comparison specialized to finite-free complexes and
nonzerodivisors on both sides of the ring map. -/
@[stacks 0F7X "finite-free integer eta base-change comparison"]
noncomputable abbrev finiteFreeComparison
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B) :=
  comparison (B := B) f K (termwiseTorsionFree f K hf)
    (scalarExtension_isTermwiseTorsionFree (B := B) K hg)

/-- In one integer degree, principality of the eta determinantal ideal makes the canonical
base-change map on eta terms bijective. -/
theorem termLinear_bijective_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Function.Bijective (termLinear (B := B) f K i) := sorry

/-- In one integer degree, the bundled canonical comparison is an isomorphism under the same
local principal-ideal hypotheses. -/
theorem termHom_isIso_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (termHom (B := B) f K i) := sorry

/-- If every integer eta determinantal ideal is principal, the canonical base-change comparison
is an isomorphism; this strengthened form only assumes the regularity needed to define its two
eta complexes. -/
theorem comparison_isIso_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K))
    [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℤ, (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (comparison (B := B) f K hK hbase) := sorry

/-- Lemma 15.97.6, Tag 0F7X: for a bounded finite-free integer-indexed complex with principal
eta determinantal ideals, the canonical eta base-change comparison is an isomorphism. -/
@[stacks 0F7X "base change for the integer-indexed Berthelot-Ogus eta complex"]
theorem comparison_isIso
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hbounded : CochainComplex.bounded (ModuleCat.{max v w} A) K)
    [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℤ, (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsIso (finiteFreeComparison (B := B) f K hf hg) := sorry

end CochainComplex.BerthelotOgus.Int.BaseChange
