/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Module
public import ReasLib.Algebra.Homology.HomologicalComplex.Admissible

@[expose] public section

/-!
# Admissibility for Cochain Complexes

This leaf specializes graded-forgetful admissibility to cochain complexes.
It exposes both the general cochain-complex API and the established
differential-graded-module names for complexes of modules over a ring.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

section

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- The canonical functor from cochain complexes to graded objects, obtained by forgetting the
differential. -/
abbrev forgetToGraded : CochainComplex C ℤ ⥤ GradedObject ℤ C :=
  HomologicalComplex.forget C (ComplexShape.up ℤ)

/-- The component of a morphism after forgetting the differential is its component as a cochain
map. -/
@[simp]
theorem forgetToGraded_map_apply {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (forgetToGraded C).map f n = f.f n := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A cochain map is admissibly monic for the graded-forgetful functor exactly when every
component is split monic. -/
theorem isAdmissibleMono_iff_termwiseSplitMono
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    IsAdmissibleMono (forgetToGraded C) f ↔ ∀ n : ℤ, IsSplitMono (f.f n) := sorry

/-- A cochain map is admissibly epic for the graded-forgetful functor exactly when every
component is split epic. -/
theorem isAdmissibleEpi_iff_termwiseSplitEpi
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    IsAdmissibleEpi (forgetToGraded C) f ↔ ∀ n : ℤ, IsSplitEpi (f.f n) := sorry

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short complex of cochain complexes is admissibly short exact for the graded-forgetful
functor exactly when it admits a splitting in every degree. -/
theorem isAdmissibleShortExact_iff_nonempty_degreewiseSplitting
    (S : ShortComplex (CochainComplex C ℤ)) :
    IsAdmissibleShortExact (forgetToGraded C) S ↔
      Nonempty (∀ n : ℤ, (ShortComplex.degreewise S n).Splitting) := sorry

end

section

variable {A : Type u} [Ring A]

/-- The canonical graded-forgetful functor for differential graded `A`-modules represented by
cochain complexes of `A`-modules. -/
abbrev dgModuleUnderlyingGradedHomSystem :
    CochainComplex (ModuleCat A) ℤ ⥤ GradedObject ℤ (ModuleCat A) :=
  forgetToGraded (ModuleCat A)

/-- Applying the DG-module graded-forgetful functor to a cochain map retains its degreewise
components. -/
@[simp]
theorem dgModuleUnderlyingGradedHomSystem_ofHom
    {K L : CochainComplex (ModuleCat A) ℤ} (f : K ⟶ L) (n : ℤ) :
    dgModuleUnderlyingGradedHomSystem.map f n = f.f n := sorry

/-- An admissible monomorphism of differential graded `A`-modules is termwise split monic. -/
theorem termwiseSplitMono_of_admissibleMono
    {K L : CochainComplex (ModuleCat A) ℤ} {f : K ⟶ L}
    (hf : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem f) :
    ∀ n : ℤ, IsSplitMono (f.f n) := sorry

/-- A termwise split monomorphism of differential graded `A`-modules is admissible after
forgetting the differential. -/
theorem isAdmissibleMono_of_termwiseSplitMono
    {K L : CochainComplex (ModuleCat A) ℤ} {f : K ⟶ L}
    (hf : ∀ n : ℤ, IsSplitMono (f.f n)) :
    IsAdmissibleMono dgModuleUnderlyingGradedHomSystem f := sorry

/-- An admissible epimorphism of differential graded `A`-modules is termwise split epic. -/
theorem termwiseSplitEpi_of_admissibleEpi
    {K L : CochainComplex (ModuleCat A) ℤ} {f : K ⟶ L}
    (hf : IsAdmissibleEpi dgModuleUnderlyingGradedHomSystem f) :
    ∀ n : ℤ, IsSplitEpi (f.f n) := sorry

/-- A termwise split epimorphism of differential graded `A`-modules is admissible after
forgetting the differential. -/
theorem isAdmissibleEpi_of_termwiseSplitEpi
    {K L : CochainComplex (ModuleCat A) ℤ} {f : K ⟶ L}
    (hf : ∀ n : ℤ, IsSplitEpi (f.f n)) :
    IsAdmissibleEpi dgModuleUnderlyingGradedHomSystem f := sorry

end

end CochainComplex
