/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.AdicCompletion
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Completed constant complexes of finite projective adic modules

This file retains the pro-étale application names for the shared completed
constant sheaf and complex constructions on arbitrary sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Ideal.PowerQuotient Opposite ComplexShape

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Λ : Type w} [CommRing Λ]

/-- A morphism of `Λ`-modules induces a morphism of the inverse systems
`n ↦ stage I M n`. -/
def moduleQuotientSystemMap (I : Ideal Λ) {M N : ModuleCat.{w} Λ} (f : M ⟶ N) :
    CategoryTheory.ConstantSheaf.AdicCompletion.moduleSystem I M ⟶
      CategoryTheory.ConstantSheaf.AdicCompletion.moduleSystem I N :=
  CategoryTheory.ConstantSheaf.AdicCompletion.moduleSystemMap I f

/-- The identity induces the identity on the ideal-power quotient system. -/
@[simp]
theorem moduleQuotientSystemMap_id (I : Ideal Λ) (M : ModuleCat.{w} Λ) :
    moduleQuotientSystemMap I (𝟙 M) =
      𝟙 (CategoryTheory.ConstantSheaf.AdicCompletion.moduleSystem I M) := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

/-- Passage to the ideal-power quotient system preserves composition. -/
theorem moduleQuotientSystemMap_comp (I : Ideal Λ) {M N P : ModuleCat.{w} Λ}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleQuotientSystemMap I (f ≫ g) =
      moduleQuotientSystemMap I f ≫ moduleQuotientSystemMap I g := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

/-- The zero map induces the zero map on the ideal-power quotient system. -/
@[simp]
theorem moduleQuotientSystemMap_zero (I : Ideal Λ) (M N : ModuleCat.{w} Λ) :
    moduleQuotientSystemMap I (0 : M ⟶ N) = 0 := by
  ext n x
  obtain ⟨x⟩ := x
  rfl

/-- A morphism of `Λ`-modules induces a morphism of completed constant sheaves. -/
def constantAdicCompletionMap {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (I : Ideal Λ)
    [HasWeakSheafify J (ModuleCat.{w} Λ)]
    {M N : ModuleCat.{w} Λ} (f : M ⟶ N) :
    CategoryTheory.ConstantSheaf.AdicCompletion.ofModule J I M ⟶
      CategoryTheory.ConstantSheaf.AdicCompletion.ofModule J I N :=
  CategoryTheory.ConstantSheaf.AdicCompletion.map J I f

/-- Restriction of scalars along `Λ → Λ^∧`. -/
abbrev restrictScalarsAdic (I : Ideal Λ) :
    ModuleCat.{w} (AdicCompletion I Λ) ⥤ ModuleCat.{w} Λ :=
  ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ))

/-- Restriction of scalars along `Λ → Λ^∧` is the change-of-rings functor. -/
theorem restrictScalarsAdic_def (I : Ideal Λ) :
    restrictScalarsAdic I =
      ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ)) :=
  rfl

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (I : Ideal Λ)
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]

/-- The completed constant sheaf of a `Λ^∧`-module, viewed as a sheaf of
`Λ`-modules: `underline{M}^∧ = lim_n underline{stage I M n}`. -/
def constantAdicCompletionSheaf (M : ModuleCat.{w} (AdicCompletion I Λ)) :
    Sheaf J (ModuleCat.{w} Λ) :=
  CategoryTheory.ConstantSheaf.AdicCompletion.ofAdicModule J I M

/-- `constantAdicCompletionSheaf` is the completed constant sheaf of the
restriction of scalars of `M`. -/
theorem constantAdicCompletionSheaf_def (M : ModuleCat.{w} (AdicCompletion I Λ)) :
    constantAdicCompletionSheaf J I M =
      CategoryTheory.ConstantSheaf.AdicCompletion.ofModule J I
        ((restrictScalarsAdic I).obj M) :=
  rfl

/-- Projection of `underline{M}^∧` onto the `n`th constant quotient sheaf. -/
def constantAdicCompletionSheaf_π (M : ModuleCat.{w} (AdicCompletion I Λ))
    (n : ℕ) :
    constantAdicCompletionSheaf J I M ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).obj
        (stage I ((restrictScalarsAdic I).obj M) n) :=
  CategoryTheory.ConstantSheaf.AdicCompletion.ofModule_π J I
    ((restrictScalarsAdic I).obj M) n

/-- The functor sending a `Λ^∧`-module to its completed constant sheaf of
`Λ`-modules. -/
def constantAdicCompletionFunctor :
    ModuleCat.{w} (AdicCompletion I Λ) ⥤ Sheaf J (ModuleCat.{w} Λ) :=
  CategoryTheory.ConstantSheaf.AdicCompletion.ofAdicModuleFunctor J I

/-- The functor evaluates to `constantAdicCompletionSheaf` on objects. -/
theorem constantAdicCompletionFunctor_obj
    (M : ModuleCat.{w} (AdicCompletion I Λ)) :
    (constantAdicCompletionFunctor J I).obj M =
      constantAdicCompletionSheaf J I M :=
  rfl

variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]

/-- The completed-constant functor preserves zero morphisms. -/
instance constantAdicCompletionFunctor_preservesZeroMorphisms :
    (constantAdicCompletionFunctor J I).PreservesZeroMorphisms :=
  CategoryTheory.ConstantSheaf.AdicCompletion.ofAdicModuleFunctor_preservesZeroMorphisms J I

/-- Degreewise completed constant sheaves, with constant differentials, of a
cochain complex of `Λ^∧`-modules. -/
abbrev constantAdicCompletionComplex :
    CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ ⥤
      CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  CategoryTheory.ConstantSheaf.AdicCompletion.ofAdicModuleComplex J I

/-- `constantAdicCompletionComplex` is `mapHomologicalComplex` of the completed
constant sheaf functor. -/
theorem constantAdicCompletionComplex_def :
    constantAdicCompletionComplex J I =
      (constantAdicCompletionFunctor J I).mapHomologicalComplex (up ℤ) :=
  rfl

/-- In each degree, the completed constant complex is the completed constant
sheaf of that term. -/
theorem constantAdicCompletionComplex_X
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ) (n : ℤ) :
    ((constantAdicCompletionComplex J I).obj M).X n =
      constantAdicCompletionSheaf J I (M.X n) :=
  rfl

end AlgebraicGeometry.Scheme.ProEt
