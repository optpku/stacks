/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition.Locus

/-!
# Cohomology after the eta decomposition quotient

Killing the total decomposition ideal makes every reduced eta pair product-shaped.  The
differential then splits between finite projective summands, so the scalar-extended eta complex
has finite locally free cohomology in every degree.

@stack 0F81
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Int.Reduction.Decomposition

variable {A : Type u} [CommRing A]

/-- The integer eta complex after scalar extension to its canonical decomposition quotient. -/
@[stacks 0F81 "eta complex over the decomposition quotient"]
noncomputable def quotientComplex
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsTermwiseFiniteFree] :
    CochainComplex (ModuleCat.{max u v} (Quotient f K)) ℤ :=
  ((ModuleCat.extendScalars
      (algebraMap A (Quotient f K))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
    ((Int.functor (f : A)).obj (Int.finiteFreeDomain f K))

/-- Without a boundedness assumption, killing all degreewise decomposition ideals already makes
every cohomology module of the scalar-extended eta complex finite locally free. -/
theorem homology_finiteLocallyFree_of_isPrincipal
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal)
    (i : ℤ) :
    Module.FiniteLocallyFree (Quotient f K) ((quotientComplex f K).homology i) := sorry

/-- Lemma 15.97.9 (5), Tag 0F81: the cohomology of `eta f K` after extension to the eta
decomposition quotient is finite locally free. -/
@[stacks 0F81 "finite locally free cohomology over the eta decomposition quotient"]
theorem homology_finiteLocallyFree
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{max u v} A) K)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal)
    (i : ℤ) :
    Module.FiniteLocallyFree (Quotient f K) ((quotientComplex f K).homology i) := sorry

end CochainComplex.BerthelotOgus.Int.Reduction.Decomposition
