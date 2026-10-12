/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Reduction
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein
public import ReasLib.LinearAlgebra.ProductRange

/-!
# The reduced coordinate pair of the integer-indexed eta complex

In divided-differential coordinates, the source term of the Berthelot-Ogus eta complex consists
of `x` such that `d x = f • y`.  Modulo `f`, the canonical pair is therefore

`x ↦ (x, y) : eta(f, K)^i / f ⟶ K^i / f × K^(i + 1) / f`.

These two target factors are the coordinate forms of
`f^i K^i / f^(i + 1) K^i` and `f^(i + 1) K^(i + 1) / f^(i + 2) K^(i + 1)`.
This formulation works uniformly in every integer degree.

@stack 0F7W
@stack 0F7Z
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int.Pair

variable {A : Type u} [CommRing A]

/-- The divided-coordinate pair `(1, d / f)` under the single degree-local regularity
hypothesis needed to divide the differential. -/
@[stacks 0F7W "degree-local divided-coordinate eta pair"]
noncomputable def linearOfRegular
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) :
    Int.term f K i →ₗ[A] K.X i × K.X (i + 1) :=
  LinearMap.prod (Int.term f K i).subtype
    (Int.divideLinear f K i hnext)

/-- Evaluation of the degree-local divided-coordinate pair. -/
@[simp]
theorem linearOfRegular_apply
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) (x : Int.term f K i) :
    linearOfRegular f K i hnext x =
      ((Int.term f K i).subtype x, Int.divideLinear f K i hnext x) := sorry

/-- The degree-local divided-coordinate pair is injective. -/
theorem linearOfRegular_injective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hnext : IsSMulRegular (K.X (i + 1)) f) :
    Function.Injective (linearOfRegular f K i hnext) := sorry

/-- The divided-coordinate pair with a source-facing termwise regularity proof. -/
@[stacks 0F7W "source-facing divided-coordinate eta pair"]
noncomputable def pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : Int.IsTermwiseTorsionFree f K) :
    Int.term f K i →ₗ[A] K.X i × K.X (i + 1) :=
  linearOfRegular f K i (hK.degree (i + 1))

/-- Evaluation of the divided-coordinate pair records the eta element and its divided
differential. -/
@[simp]
theorem pairLinear_apply
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : Int.IsTermwiseTorsionFree f K) (x : Int.term f K i) :
    pairLinear f K i hK x =
      ((Int.term f K i).subtype x,
        Int.divideLinear f K i (hK.degree (i + 1)) x) := sorry

/-- The divided-coordinate eta pair is injective. -/
theorem pairLinear_injective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : Int.IsTermwiseTorsionFree f K) :
    Function.Injective (pairLinear f K i hK) := sorry

/-- The source-facing divided-coordinate eta pair is a monomorphism in `ModuleCat`. -/
theorem pairLinear_mono
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : Int.IsTermwiseTorsionFree f K) :
    Mono (ModuleCat.ofHom (pairLinear f K i hK)) := sorry

/-- The divided-coordinate pair on the canonical regular domain.  This is the preferred
downstream interface; the regularity proof is carried by `K`. -/
@[stacks 0F7W "divided-coordinate pair on the integer eta domain"]
noncomputable def linear (f : A) (K : Int.Domain f) (i : ℤ) :
    Int.term f K.obj i →ₗ[A] K.obj.X i × K.obj.X (i + 1) :=
  linearOfRegular f K.obj i (K.property.degree (i + 1))

/-- Evaluation of the canonical-domain pair records the eta element and its divided
differential. -/
@[simp]
theorem linear_apply (f : A) (K : Int.Domain f) (i : ℤ) (x : Int.term f K.obj i) :
    linear f K i x =
      ((Int.term f K.obj i).subtype x,
        Int.divideLinear f K.obj i (K.property.degree (i + 1)) x) := sorry

/-- The divided-coordinate pair is injective on every object of the regular domain. -/
theorem linear_injective (f : A) (K : Int.Domain f) (i : ℤ) :
    Function.Injective (linear f K i) := sorry

/-- The divided-coordinate pair on the regular domain is a monomorphism in `ModuleCat`. -/
@[stacks 0F7W "monomorphism of the divided-coordinate eta pair"]
instance linear_mono (f : A) (K : Int.Domain f) (i : ℤ) :
    Mono (ModuleCat.ofHom (linear f K i)) := sorry

end CochainComplex.BerthelotOgus.Int.Pair

namespace CochainComplex.BerthelotOgus.Int.Reduction.Pair

variable {A : Type u} [CommRing A]

/-- The second coordinate of the reduced eta pair, obtained by dividing the differential by `f`
and then reducing modulo `(f)`. -/
@[stacks 0F7Z "second coordinate of the reduced eta pair"]
noncomputable def nextLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i →ₗ[A ⧸ principalIdeal f] (ambientComplex f K).X (i + 1) :=
  LinearMap.IdealQuotient.map (Int.divideLinear f K i (hK.degree (i + 1))) (principalIdeal f)

/-- On quotient generators, the second coordinate is represented by the divided differential. -/
theorem nextLinear_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (x : Int.term f K i) :
    nextLinear f K i hK (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Int.divideLinear f K i (hK.degree (i + 1)) x) := sorry

/-- The reduced coordinate pair `(1, d / f)` of the integer-indexed eta complex. -/
@[stacks 0F7Z "reduced divided-coordinate eta pair"]
noncomputable def pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i →ₗ[A ⧸ principalIdeal f]
      (ambientComplex f K).X i × (ambientComplex f K).X (i + 1) :=
  LinearMap.prod (quotientLinear f K i hK) (nextLinear f K i hK)

/-- The first coordinate of the reduced eta pair is the reduced term inclusion. -/
@[simp]
theorem fst_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (LinearMap.fst (A ⧸ principalIdeal f) _ _).comp (pairLinear f K i hK) =
      quotientLinear f K i hK := sorry

/-- The second coordinate of the reduced eta pair is the divided differential modulo `f`. -/
@[simp]
theorem snd_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (LinearMap.snd (A ⧸ principalIdeal f) _ _).comp (pairLinear f K i hK) =
      nextLinear f K i hK := sorry

/-- On a quotient generator, the reduced eta pair is represented by the element and its divided
differential. -/
theorem pairLinear_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (x : Int.term f K i) :
    pairLinear f K i hK (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((Int.term f K i).subtype x),
        Submodule.Quotient.mk (Int.divideLinear f K i (hK.degree (i + 1)) x)) := sorry

/-- The reduced pair detects a reduced eta term: if both its underlying element and divided
differential vanish modulo `f`, then the eta term itself is divisible by `f` inside the eta
submodule. -/
theorem pairLinear_injective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    Function.Injective (pairLinear f K i hK) := sorry

/-- The reduced coordinate pair on the canonical regular domain.  This is the preferred
downstream interface. -/
@[stacks 0F7Z "reduced coordinate pair on the integer eta domain"]
noncomputable def linear (f : A) (K : Int.Domain f) (i : ℤ) :
    (complex f K.obj K.property).X i →ₗ[A ⧸ principalIdeal f]
      (ambientComplex f K.obj).X i × (ambientComplex f K.obj).X (i + 1) :=
  pairLinear f K.obj i K.property

/-- The first coordinate of the canonical-domain reduced pair is the reduced term
inclusion. -/
@[simp]
theorem fst_comp_linear (f : A) (K : Int.Domain f) (i : ℤ) :
    (LinearMap.fst (A ⧸ principalIdeal f) _ _).comp (linear f K i) =
      quotientLinear f K.obj i K.property := sorry

/-- The second coordinate of the canonical-domain reduced pair is the divided differential
modulo `f`. -/
@[simp]
theorem snd_comp_linear (f : A) (K : Int.Domain f) (i : ℤ) :
    (LinearMap.snd (A ⧸ principalIdeal f) _ _).comp (linear f K i) =
      nextLinear f K.obj i K.property := sorry

/-- Evaluation of the canonical-domain reduced pair on a quotient generator. -/
theorem linear_mk (f : A) (K : Int.Domain f) (i : ℤ) (x : Int.term f K.obj i) :
    linear f K i (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((Int.term f K.obj i).subtype x),
        Submodule.Quotient.mk
          (Int.divideLinear f K.obj i (K.property.degree (i + 1)) x)) := sorry

/-- The reduced coordinate pair is injective on every object of the regular domain. -/
theorem linear_injective (f : A) (K : Int.Domain f) (i : ℤ) :
    Function.Injective (linear f K i) := sorry

/-- Surjectivity on cycles from `K / (f)^2 K` to `K / fK` makes the range of the reduced eta pair
the product of its two coordinate ranges. -/
theorem pairLinear_rangeIsProduct_of_cyclesLift
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hcycles : Bockstein.CyclesLift f K i) :
    (pairLinear f K i hK).rangeIsProduct := sorry

/-- The reduced eta pair identifies its source with a product of submodules whenever cycles lift
from reduction modulo `(f)^2` to reduction modulo `(f)`. -/
theorem pairLinear_identifiesWithProdSubmodules
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hcycles : Bockstein.CyclesLift f K i) :
    (pairLinear f K i hK).identifiesWithProdSubmodules := sorry

/-- Cycles lifting modulo `f` makes the range of the canonical-domain reduced pair a
product. -/
theorem rangeIsProduct_of_cyclesLift
    (f : A) (K : Int.Domain f) (i : ℤ) (hcycles : Bockstein.CyclesLift f K.obj i) :
    (linear f K i).rangeIsProduct := sorry

/-- Cycles lifting modulo `f` identifies the canonical-domain reduced pair with the product of
its coordinate ranges. -/
theorem identifiesWithProdSubmodules
    (f : A) (K : Int.Domain f) (i : ℤ) (hcycles : Bockstein.CyclesLift f K.obj i) :
    (linear f K i).identifiesWithProdSubmodules := sorry

/-- Lemma 15.96.8, tag `0F7Z`: for a nonzerodivisor acting regularly termwise, surjectivity on
reduced cycles makes the canonical reduced eta pair identify its source with a product of
submodules of its two target factors. -/
@[stacks 0F7Z "product decomposition for the reduced Berthelot-Ogus eta pair"]
theorem pairLinear_identifiesWithProdSubmodules_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K)
    (hcycles : Bockstein.CyclesLift f K i) :
    (pairLinear f K i hK).identifiesWithProdSubmodules := sorry

end CochainComplex.BerthelotOgus.Int.Reduction.Pair
