/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.FiniteLocallyFree
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

/-!
# Finite-projective terms of integer-indexed eta reduction

Finite local freeness of an eta term descends to its reduction modulo `(f)`.  The ambient target
terms are ordinary quotient modules, so projectivity is inherited directly from the original
terms.  These facts supply the hypotheses of the product-splitting locus API.
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Int.Reduction

variable {A : Type u} [CommRing A]

/-- A reduced integer eta term is finite under the degree-local principal-ideal hypothesis. -/
theorem term_finite_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hreg : Int.IsTermwiseTorsionFree f K)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (Int.etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.Finite (A ⧸ principalIdeal f) ((complex f K hreg).X i) := sorry

/-- A reduced integer eta term is projective under the degree-local principal-ideal
hypothesis. -/
theorem term_projective_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hreg : Int.IsTermwiseTorsionFree f K)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (Int.etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.Projective (A ⧸ principalIdeal f) ((complex f K hreg).X i) := sorry

/-- An ambient term reduced modulo `(f)` is finite when the original term is finite. -/
theorem ambientTerm_finite
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Finite A (K.X i)] :
    Module.Finite (A ⧸ principalIdeal f) ((ambientComplex f K).X i) := sorry

/-- An ambient term reduced modulo `(f)` is projective when the original term is projective. -/
theorem ambientTerm_projective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Projective A (K.X i)] :
    Module.Projective (A ⧸ principalIdeal f) ((ambientComplex f K).X i) := sorry

namespace Pair

/-- The reduced divided-coordinate eta pair on the canonical regular domain is a split
monomorphism under the degree-local principal-ideal hypothesis. -/
theorem linear_isSplitMono
    (f : A) (K : Int.Domain f) (i : ℤ)
    [Module.Free A (K.obj.X i)] [Module.Finite A (K.obj.X i)]
    [Module.Free A (K.obj.X (i + 1))] [Module.Finite A (K.obj.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (Int.etaDeterminantalIdeal f K.obj i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (linear f K i)) := sorry

/-- The reduced divided-coordinate eta pair is a split monomorphism under the degree-local
principal-ideal hypothesis. -/
theorem pairLinear_isSplitMono_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hreg : Int.IsTermwiseTorsionFree f K)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (Int.etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K i hreg)) := sorry

end Pair

end CochainComplex.BerthelotOgus.Int.Reduction
