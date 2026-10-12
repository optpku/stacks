/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Concentrated
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.Kernel
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.QuasiIso
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Equivalence
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Graded Morita Realizations

This leaf states the reusable output of the DG Morita realization argument.  The realization is
an actual differential graded bimodule representing the image of the regular module.  It does
not assert that the original equivalence is itself definitionally or naturally a derived tensor
functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v uDA uDB vDA vDB

namespace CochainDGAlgebra.DerivedMorita

variable {R : Type u} [CommRing R]

/-- The regular module as an object of a chosen derived localization. -/
@[stacks 09SA "regular object in a chosen derived localization"]
abbrev regularObjectFor {A : CochainDGAlgebra.{u, v} R}
    {DA : Type uDA} [Category.{vDA} DA]
    (localizeA : K R (DifferentialGradedModule.{u, v} A) ⥤ DA) : DA :=
  localizeA.obj ⟨A.regularModule⟩

/-- The object represented by the underlying right module of a differential graded bimodule in
a chosen derived localization. -/
@[stacks 09SA "bimodule object in a chosen derived localization"]
abbrev bimoduleObjectFor {A B : CochainDGAlgebra.{u, v} R}
    {DB : Type uDB} [Category.{vDB} DB]
    (localizeB : K R (DifferentialGradedModule.{u, v} B) ⥤ DB)
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) : DB :=
  localizeB.obj N.rightHomotopyObject

/-- The arbitrary-localization form of the DG Morita realization theorem. It produces a
bimodule representing the image of the regular module in any chosen localizations compatible
with the triangulated and `R`-linear structures. -/
@[stacks 09SA "DG Morita realization for chosen localizations"]
theorem exists_bimodule_of_localizations
    (A B : CochainDGAlgebra.{u, v} R)
    (hA : A.IsConcentratedInDegreeZero) (hB : B.IsKFlat)
    {DA : Type uDA} {DB : Type uDB}
    [Category.{vDA} DA] [Category.{vDB} DB]
    [HasZeroObject DA] [HasZeroObject DB]
    [Preadditive DA] [Preadditive DB]
    [Linear R DA] [Linear R DB]
    [HasCoproducts.{vDA} DA] [HasCoproducts.{vDB} DB]
    [HasShift DA ℤ] [HasShift DB ℤ]
    [∀ n : ℤ, (shiftFunctor DA n).Additive]
    [∀ n : ℤ, (shiftFunctor DB n).Additive]
    [Pretriangulated DA] [Pretriangulated DB]
    (localizeA : K R (DifferentialGradedModule.{u, v} A) ⥤ DA)
    [localizeA.IsLocalization (DifferentialGradedModule.quasiIso A)]
    [localizeA.CommShift ℤ] [localizeA.IsTriangulated] [localizeA.Linear R]
    (localizeB : K R (DifferentialGradedModule.{u, v} B) ⥤ DB)
    [localizeB.IsLocalization (DifferentialGradedModule.quasiIso B)]
    [localizeB.CommShift ℤ] [localizeB.IsTriangulated] [localizeB.Linear R]
    (e : RLinear.TriangulatedEquivalence R DA DB) :
    ∃ (N : DifferentialGradedBimodule.{u, v, v, v} A B)
      (_ : e.functor.obj (regularObjectFor localizeA) ≅ bimoduleObjectFor localizeB N),
      N.IsMoritaKernelFor localizeB := sorry

/-- Proposition 22.37.6 (09SA): let `A` and `B` be cochain differential graded `R`-algebras,
with `A` concentrated in degree zero and `B` K-flat. Given an `R`-linear triangulated
equivalence of their canonical derived categories, there is a differential graded `(A, B)`-
bimodule whose underlying right module represents the image of the regular `A`-module. That
representative is compact and is a weak generator, and its canonical self-extension comparison
is bijective in every degree.

The comparison is only object-level; no natural isomorphism between the given equivalence and a
derived tensor functor is asserted. -/
@[stacks 09SA]
theorem exists_bimodule
    (A B : CochainDGAlgebra.{u, v} R)
    (hA : A.IsConcentratedInDegreeZero) (hB : B.IsKFlat)
    (e : RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category.{u, v} A)
      (DifferentialGradedModule.Derived.Category.{u, v} B)) :
    ∃ (N : DifferentialGradedBimodule.{u, v, v, v} A B)
      (_ : e.functor.obj (DifferentialGradedModule.Derived.regularObject A) ≅
        N.rightDerivedObject),
      N.IsMoritaKernel := sorry

end CochainDGAlgebra.DerivedMorita
