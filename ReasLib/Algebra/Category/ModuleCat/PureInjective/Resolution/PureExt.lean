/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution
public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution.HomComplex
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.PureInjectiveCoresolution

variable {A : Type u} [CommRing A]
variable {N : ModuleCat.{v} A}

/-- The integer-indexed cochain complex obtained by extending a coresolution by zero in
negative degrees. -/
noncomputable def cochainComplex (I : PureInjectiveCoresolution N) :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  I.cocomplex.extend ComplexShape.embeddingUpNat

/-- The module-valued Hom complex from a module concentrated in degree zero to a chosen
pure injective coresolution. -/
noncomputable def homComplex (I : PureInjectiveCoresolution N) (M : ModuleCat.{v} A) :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  CochainComplex.HomComplex.moduleComplex A
    ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj M) I.cochainComplex

/-- The degree-`i` pure extension module is the `i`th homology object of the module-valued
Hom complex associated to a chosen pure injective coresolution. -/
noncomputable def pureExt (I : PureInjectiveCoresolution N) (M : ModuleCat.{v} A) (i : ℕ) :
    ModuleCat.{v} A :=
  (I.homComplex M).homology (i : ℤ)

/-- Positive-degree pure extensions vanish when the target module is pure injective. -/
theorem pureExt_isZero_of_pureInjective
    {M : ModuleCat.{v} A} (I : PureInjectiveCoresolution N) (hN : N.PureInjective)
    (i : ℕ) (hi : 0 < i) :
    IsZero (I.pureExt M i) := sorry

/-- Positive-degree pure extensions vanish when the source module is pure projective. -/
theorem pureExt_isZero_of_pureProjective
    {M : ModuleCat.{v} A} (I : PureInjectiveCoresolution N) (hM : M.PureProjective)
    (i : ℕ) (hi : 0 < i) :
    IsZero (I.pureExt M i) := sorry

/-- Positive-degree pure extensions vanish for finitely presented source modules. -/
theorem pureExt_isZero_of_finitePresentation
    {M : ModuleCat.{v} A} (I : PureInjectiveCoresolution N)
    [Module.FinitePresentation A M] (i : ℕ) (hi : 0 < i) :
    IsZero (I.pureExt M i) := sorry

/-- A pure projective resolution computes pure extensions by the homology of its Hom complex. -/
theorem pureExt_isIsomorphic_homology
    {M : ModuleCat.{v} A} (I : PureInjectiveCoresolution N)
    (P : ModuleCat.PureProjectiveResolution M) (i : ℕ) :
    IsIsomorphic (I.pureExt M i) ((P.homComplex N).homology (i : ℤ)) := sorry

end ModuleCat.PureInjectiveCoresolution
