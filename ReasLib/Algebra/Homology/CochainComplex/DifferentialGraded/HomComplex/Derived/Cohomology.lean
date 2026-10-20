/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology.Over

/-!
# Integral compatibility facade for enriched Hom cohomology

The reusable owner is
`CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology`, parameterized by a commutative
base ring.  This file keeps the historical `R := ℤ` names used by existing consumers without
introducing a second model, localization, or comparison API.
-/

@[expose] public section

noncomputable section

universe u v w g

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open CategoryTheory.CochainComplex.Enriched.Over
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched.RHom.Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]

/-- The historical integral name for the generic K-injective model category. -/
@[stacks 0CS6 "integral K-injective Hom model category"]
abbrev Model :=
  Over.RHom.Cohomology.Model (R := ℤ) (C := C)

/-- The historical integral name for the generic product denominator system. -/
@[stacks 0CS6 "integral K-injective Hom denominators"]
abbrev modelQis : MorphismProperty ((Model (C := C))ᵒᵖ × Model (C := C)) :=
  Over.RHom.Cohomology.modelQis (R := ℤ) (C := C)

/-- The historical integral name for the K-injective model inclusion. -/
@[stacks 0CS6 "integral K-injective Hom model inclusion"]
abbrev modelInclusion :
    (Model (C := C))ᵒᵖ × Model (C := C) ⥤
      (DifferentialGradedCategory.K ℤ (CochainComplex C ℤ))ᵒᵖ ×
        DifferentialGradedCategory.K ℤ (CochainComplex C ℤ) :=
  Over.RHom.Cohomology.modelInclusion (R := ℤ) (C := C)

/-- The historical integral name for the K-injective localization. -/
noncomputable abbrev modelLocalization :
    (Model (C := C))ᵒᵖ × Model (C := C) ⥤
      (DerivedCategory.{w} C)ᵒᵖ × DerivedCategory.{w} C :=
  Over.RHom.Cohomology.modelLocalization (R := ℤ) (C := C)

section DerivedHom

variable [CategoryTheory.CochainComplex.Enriched.Over.RHom.Has (R := ℤ) (C := C)]

/-- The historical integral name for degree-`n` derived Hom cohomology. -/
noncomputable abbrev functor (n : ℤ) :=
  Over.RHom.Cohomology.functor (R := ℤ) (C := C) n

/-- The historical integral name for lifted degree-`n` derived Hom cohomology. -/
noncomputable abbrev uliftFunctor (n : ℤ) :
    (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ ModuleCat.{max v w} ℤ :=
  Over.RHom.Cohomology.uliftFunctor (R := ℤ) (C := C) n

end DerivedHom

/-- The historical integral name for the strict Hom model. -/
noncomputable abbrev modelHom :
    (Model (C := C))ᵒᵖ × Model (C := C) ⥤ DerivedCategory (ModuleCat.{v} ℤ) :=
  Over.RHom.Cohomology.modelHom (R := ℤ) (C := C)

/-- The historical integral name for strict Hom cohomology. -/
noncomputable abbrev modelCohomology (n : ℤ) :
    (Model (C := C))ᵒᵖ × Model (C := C) ⥤ ModuleCat.{max v w} ℤ :=
  Over.RHom.Cohomology.modelCohomology (R := ℤ) (C := C) n

/-- The historical integral name for the shifted-Hom target. -/
noncomputable abbrev shiftedFunctor (n : ℤ) :
    (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ ModuleCat.{max v w} ℤ :=
  Over.RHom.Cohomology.shiftedFunctor (R := ℤ) (C := C) n

/-- The historical integral name for the shifted-Hom model restriction. -/
noncomputable abbrev modelShifted (n : ℤ) :
    (Model (C := C))ᵒᵖ × Model (C := C) ⥤ ModuleCat.{max v w} ℤ :=
  Over.RHom.Cohomology.modelShifted (R := ℤ) (C := C) n

/-- The historical integral name for removing the universe lift. -/
noncomputable abbrev modelCohomologyDown
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelCohomologyDown (R := ℤ) (C := C) X n

/-- The historical integral name for strict Hom homology comparison. -/
noncomputable abbrev modelHomologyEquiv
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelHomologyEquiv (R := ℤ) (C := C) X n

/-- The historical integral name for the K-injective Ext comparison. -/
noncomputable abbrev modelExtEquiv
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelExtEquiv (R := ℤ) (C := C) X n

/-- The historical integral name for endpoint transport. -/
noncomputable abbrev modelEndpointEquiv
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelEndpointEquiv (R := ℤ) (C := C) X n

/-- The historical integral name for lifting shifted Hom. -/
noncomputable abbrev modelShiftedUp
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelShiftedUp (R := ℤ) (C := C) X n

/-- The historical integral name for the model linear equivalence. -/
noncomputable abbrev modelLinearEquiv
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelLinearEquiv (R := ℤ) (C := C) X n

/-- Pointwise evaluation of the historical integral model equivalence. -/
@[simp]
theorem modelLinearEquiv_apply
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ)
    (x : (modelCohomology (C := C) n).obj X) :
    modelLinearEquiv (C := C) X n x =
      modelShiftedUp (C := C) X n
        (modelEndpointEquiv (C := C) X n
          (modelExtEquiv (C := C) X n
            (modelHomologyEquiv (C := C) X n
              (modelCohomologyDown (C := C) X n x)))) := sorry

section DerivedHomComparison

variable [CategoryTheory.CochainComplex.Enriched.Over.RHom.Has (R := ℤ) (C := C)]

/-- The historical integral K-injective cohomology comparison component. -/
noncomputable abbrev modelCohomologyAppIso
    (X : (Model (C := C))ᵒᵖ × Model (C := C)) (n : ℤ) :=
  Over.RHom.Cohomology.modelCohomologyAppIso (R := ℤ) (C := C) X n

/-- Naturality of the historical integral K-injective cohomology comparison. -/
@[reassoc]
theorem modelCohomologyAppIso_naturality (n : ℤ)
    {X Y : (Model (C := C))ᵒᵖ × Model (C := C)} (f : X ⟶ Y) :
    (modelLocalization (C := C) ⋙ uliftFunctor (C := C) n).map f ≫
        (modelCohomologyAppIso (C := C) Y n).hom =
      (modelCohomologyAppIso (C := C) X n).hom ≫
        (modelCohomology (C := C) n).map f := sorry

/-- The historical integral K-injective cohomology model isomorphism. -/
noncomputable abbrev modelCohomologyIso (n : ℤ) :=
  Over.RHom.Cohomology.modelCohomologyIso (R := ℤ) (C := C) n

end DerivedHomComparison

/-- Naturality of the historical integral model equivalence. -/
@[reassoc]
theorem modelLinearEquiv_naturality (n : ℤ)
    {X Y : (Model (C := C))ᵒᵖ × Model (C := C)} (f : X ⟶ Y) :
    (modelCohomology (C := C) n).map f ≫
        (modelLinearEquiv (C := C) Y n).toModuleIso.hom =
      (modelLinearEquiv (C := C) X n).toModuleIso.hom ≫
        (modelShifted (C := C) n).map f := sorry

/-- The historical integral strict model isomorphism. -/
noncomputable abbrev modelIso (n : ℤ) :=
  Over.RHom.Cohomology.modelIso (R := ℤ) (C := C) n

section DerivedHomComparison

variable [CategoryTheory.CochainComplex.Enriched.Over.RHom.Has (R := ℤ) (C := C)]

/-- The historical integral K-injective restriction comparison. -/
noncomputable abbrev modelComparisonIso (n : ℤ) :=
  Over.RHom.Cohomology.modelComparisonIso (R := ℤ) (C := C) n

end DerivedHomComparison

section Grothendieck

variable [IsGrothendieckAbelian.{g} C]

/-- The historical integral global cohomology representation. -/
noncomputable abbrev iso (n : ℤ) :=
  Over.RHom.Cohomology.iso (R := ℤ) (C := C) n

/-- The historical integral unlifted cohomology-to-shifted-Hom equivalence. -/
noncomputable abbrev linearEquiv (M N : DerivedCategory C) (n : ℤ) :=
  Over.RHom.Cohomology.linearEquiv (R := ℤ) (C := C) M N n

/-- Pointwise evaluation of the historical integral cohomology representation. -/
@[simp]
theorem linearEquiv_apply (M N : DerivedCategory C) (n : ℤ)
    (x : (functor (C := C) n).obj (Opposite.op M, N)) :
    linearEquiv (C := C) M N n x =
      ((iso (C := C) n).hom.app (Opposite.op M, N) (ULift.up x)).down := sorry

/-- Naturality of the historical integral cohomology representation. -/
@[reassoc]
theorem iso_naturality (n : ℤ)
    {X Y : (DerivedCategory C)ᵒᵖ × DerivedCategory C} (f : X ⟶ Y) :
    (uliftFunctor (C := C) n).map f ≫ (iso (C := C) n).hom.app Y =
      (iso (C := C) n).hom.app X ≫ (shiftedFunctor (C := C) n).map f := sorry

end Grothendieck

end CategoryTheory.CochainComplex.Enriched.RHom.Cohomology
