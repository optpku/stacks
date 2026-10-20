module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Reduction.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.LinearAlgebra.ProductRange.SplittingLocus
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.FinitePresentation

/-!
# Decomposition ideals for integer-indexed eta complexes

The splitting locus is attached to the canonical eta domain.  For a termwise finite-free complex
and a nonzerodivisor, `degreeIdeal` uses `finiteFreeDomain` and exposes no regularity proof or
principal-ideal hypothesis in its data.  The total ideal is the supremum over all integer degrees.
@stack 0F81
@stack 0GSW
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Int.Reduction.Decomposition

variable {A : Type u} [CommRing A]

/-- The product-splitting locus ideal of a reduced integer eta pair on the canonical regular
domain. -/
noncomputable def locusIdeal
    (f : A) (K : Int.Domain f) (i : ℤ) : Ideal (A ⧸ principalIdeal f) :=
  LinearMap.ProductRange.locusIdeal (Reduction.Pair.linear f K i)

/-- The locus ideal for a raw complex equipped with an explicit termwise regularity proof. -/
noncomputable def locusIdealOfRegular
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hreg : Int.IsTermwiseTorsionFree f K) : Ideal (A ⧸ principalIdeal f) :=
  locusIdeal f ⟨K, hreg⟩ i

/-- The canonical degree-`i` decomposition ideal for a finite-free complex and a bundled
nonzerodivisor. -/
@[stacks 0GSW "integer-indexed eta decomposition ideal"]
noncomputable def degreeIdeal
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [K.IsTermwiseFiniteFree] :
    Ideal (A ⧸ principalIdeal (f : A)) :=
  locusIdeal (f : A) (Int.finiteFreeDomain f K) i

/-- The locus ideal has its universal base-change property whenever the reduced pair is split
and its target terms are projective. -/
theorem locusIdeal_le_ker_iff
    (f : A) (K : Int.Domain f) (i : ℤ)
    [Module.Free A (K.obj.X i)] [Module.Finite A (K.obj.X i)]
    [Module.Free A (K.obj.X (i + 1))] [Module.Finite A (K.obj.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (Int.etaDeterminantalIdeal f K.obj i).IsPrincipal)
    (B : Type w) [CommRing B] [Algebra (A ⧸ principalIdeal f) B] :
    locusIdeal f K i ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (Reduction.Pair.linear f K i).baseChangeIdentifiesWithProdSubmodules B := sorry

/-- The canonical degree ideal cuts out exactly the base changes on which the reduced eta pair
has product-shaped image. -/
@[stacks 0GSW "universal property of the integer eta decomposition ideal"]
theorem degreeIdeal_le_ker_iff
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal)
    (B : Type w) [CommRing B] [Algebra (A ⧸ principalIdeal (f : A)) B] :
    degreeIdeal f K i ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal (f : A)) B) ↔
      LinearMap.baseChangeIdentifiesWithProdSubmodules
        (Reduction.Pair.linear (f : A) (Int.finiteFreeDomain f K) i) B := sorry

/-- The canonical degree decomposition ideal is finitely generated. -/
@[stacks 0GSW "finite generation of an integer eta decomposition ideal"]
theorem degreeIdeal_fg
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal) :
    (degreeIdeal f K i).FG := sorry

/-- The degree decomposition ideal is zero exactly when the reduced eta pair already has
product-shaped image. -/
theorem degreeIdeal_eq_bot_iff
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal) :
    degreeIdeal f K i = ⊥ ↔
      LinearMap.identifiesWithProdSubmodules
        (Reduction.Pair.linear (f : A) (Int.finiteFreeDomain f K) i) := sorry

/-- A zero source term contributes the zero degree decomposition ideal. -/
theorem degreeIdeal_eq_bot_of_isZero
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [K.IsTermwiseFiniteFree]
    (hK : IsZero (K.X i)) : degreeIdeal f K i = ⊥ := sorry

/-- The total eta decomposition ideal is the supremum of its degreewise ideals. -/
@[stacks 0F81 "total eta decomposition ideal"]
noncomputable def ideal
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] :
    Ideal (A ⧸ principalIdeal (f : A)) :=
  ⨆ i : ℤ, degreeIdeal f K i

/-- The canonical quotient by the total eta decomposition ideal. -/
@[stacks 0F81 "eta decomposition quotient"]
abbrev Quotient
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] :=
  (A ⧸ principalIdeal (f : A)) ⧸ ideal f K

/-- Lemma 15.97.9 (1), Tag 0F81: boundedness makes the total decomposition ideal a finite sum
of finitely generated degree ideals. -/
@[stacks 0F81 "finite generation of the total eta decomposition ideal"]
theorem ideal_fg
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal) :
    (ideal f K).FG := sorry

/-- Lemma 15.97.9 (2a), Tag 0F81: the canonical map to the decomposition quotient is
surjective. -/
@[stacks 0F81 "surjectivity of the eta decomposition quotient map"]
theorem quotientMap_surjective
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] :
    Function.Surjective (algebraMap (A ⧸ principalIdeal (f : A)) (Quotient f K)) := sorry

/-- Lemma 15.97.9 (2b), Tag 0F81: the decomposition quotient is finitely presented over
`A / (f)`. -/
@[stacks 0F81 "finite presentation of the eta decomposition quotient"]
theorem quotient_finitePresentation
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal) :
    Algebra.FinitePresentation (A ⧸ principalIdeal (f : A)) (Quotient f K) := sorry

end CochainComplex.BerthelotOgus.Int.Reduction.Decomposition
