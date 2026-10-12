/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ScalarPresentation.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise

/-!
# Determinantal ideals for integer-indexed Berthelot-Ogus eta presentations

This file specializes the shape-independent scalar-differential presentation to consecutive
degrees of an integer-indexed cochain complex.  The presentation quotient and its Fitting ideal
are thin views of `HomologicalComplex.ScalarPresentation`.
@stack 0F7V
@stack 0GST
@stack 0GSU
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- The map `(f, d i (i + 1))` defining the degree-`i` eta presentation. -/
@[stacks 0F7V "Berthelot-Ogus eta presentation map"]
abbrev etaPresentationMap (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    K.X i →ₗ[A] K.X i × K.X (i + 1) :=
  HomologicalComplex.ScalarPresentation.map f K i (i + 1)

/-- The quotient module presented by `(f, d i (i + 1))`. -/
@[stacks 0F7V "Berthelot-Ogus eta presentation quotient"]
abbrev etaPresentationQuotient
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :=
  HomologicalComplex.ScalarPresentation.quotient f K i (i + 1)

/-- The degree-`i` Berthelot-Ogus determinantal ideal.  Its definition only requires the source
term to be finite; freeness is needed only for the next term whose rank indexes the Fitting
ideal. -/
@[stacks 0F7V "Berthelot-Ogus eta determinantal ideal"]
def etaDeterminantalIdeal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] : Ideal A :=
  HomologicalComplex.ScalarPresentation.fittingIdeal f K i (i + 1)

/-- The integer eta determinantal ideal is the shape-independent scalar-presentation Fitting
ideal in consecutive degrees. -/
@[simp]
theorem etaDeterminantalIdeal_def
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] :
    etaDeterminantalIdeal f K i =
      HomologicalComplex.ScalarPresentation.fittingIdeal f K i (i + 1) := sorry

/-- The integer eta determinantal ideal commutes with extension of scalars.  This minimal form
does not require the scalar to be regular or the source term to be free. -/
theorem etaDeterminantalIdeal_baseChange
    {B : Type w} [CommRing B] [Algebra A B]
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))] :
    etaDeterminantalIdeal (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K) i =
      Ideal.map (algebraMap A B) (etaDeterminantalIdeal f K i) := sorry

/-- Lemma 15.97.3, Tag 0GSU: for a bounded finite-free complex, the eta determinantal ideal
commutes with a base change that preserves the chosen nonzerodivisor. -/
@[stacks 0GSU "base change of the Berthelot-Ogus eta determinantal ideal"]
theorem etaDeterminantalIdeal_baseChange_of_bounded
    {B : Type w} [CommRing B] [Algebra A B]
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K) [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B) :
    etaDeterminantalIdeal (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K) i =
      Ideal.map (algebraMap A B) (etaDeterminantalIdeal f K i) := sorry

/-- Multiplying the eta scalar by a unit induces a canonical equivalence of the consecutive-degree
presentation quotients. -/
@[stacks 0GST "unit rescaling of eta presentation quotients"]
noncomputable abbrev quotientEquivUnitMul
    (f : A) (u : Aˣ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    etaPresentationQuotient f K i ≃ₗ[A]
      etaPresentationQuotient ((u : A) * f) K i :=
  HomologicalComplex.ScalarPresentation.quotientEquivUnitMul f u K i (i + 1)

/-- The unit-rescaling equivalence of integer eta presentation quotients acts on representatives
by rescaling the first coordinate. -/
@[simp]
theorem quotientEquivUnitMul_mk
    (f : A) (u : Aˣ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (x : K.X i × K.X (i + 1)) :
    quotientEquivUnitMul f u K i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (HomologicalComplex.ScalarPresentation.unitTargetEquiv u K i (i + 1) x) := sorry

/-- Multiplying `f` by a unit does not change the degree-`i` eta determinantal ideal. -/
theorem etaDeterminantalIdeal_eq_unit_mul
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (f : A) (u : Aˣ) :
    etaDeterminantalIdeal f K i = etaDeterminantalIdeal ((u : A) * f) K i := sorry

/-- Lemma 15.97.2, Tag 0GST: multiplying a nonzerodivisor by a unit does not change the
degreewise eta determinantal ideal of a bounded finite-free complex. -/
@[stacks 0GST "unit invariance of the Berthelot-Ogus eta determinantal ideal"]
theorem etaDeterminantalIdeal_eq_unit_mul_of_bounded
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K) [K.IsTermwiseFiniteFree]
    (f : A) (hf : f ∈ nonZeroDivisors A) (u : Aˣ) :
    etaDeterminantalIdeal f K i = etaDeterminantalIdeal ((u : A) * f) K i := sorry

/-- A strict isomorphism of integer-indexed cochain complexes induces an equivalence of their eta
presentation quotients. -/
@[stacks 0F7V "eta presentation quotient under a complex isomorphism"]
noncomputable abbrev quotientEquivOfIso
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (e : K ≅ L) (i : ℤ) :
    etaPresentationQuotient f K i ≃ₗ[A] etaPresentationQuotient f L i :=
  HomologicalComplex.ScalarPresentation.quotientEquivOfIso f e i (i + 1)

/-- The strict-isomorphism equivalence of integer eta presentation quotients acts on
representatives by the two adjacent degree components. -/
@[simp]
theorem quotientEquivOfIso_mk
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (e : K ≅ L) (i : ℤ)
    (x : K.X i × K.X (i + 1)) :
    quotientEquivOfIso f e i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (HomologicalComplex.ScalarPresentation.targetEquiv e i (i + 1) x) := sorry

/-- Strict isomorphisms preserve the integer eta determinantal ideal. -/
theorem etaDeterminantalIdeal_eq_of_iso
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (e : K ≅ L) (i : ℤ)
    [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    [Module.Finite A (L.X i)]
    [Module.Free A (L.X (i + 1))] [Module.Finite A (L.X (i + 1))] :
    etaDeterminantalIdeal f K i = etaDeterminantalIdeal f L i := sorry

end CochainComplex.BerthelotOgus.Int
