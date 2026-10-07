module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Enriched
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology.Over

/-!
# Derived Hom cohomology for module sheaves over an algebra sheaf

This file is the coefficient-generic CommAlg façade for the explicit-base-ring cohomology
owner.  The K-injective model, localization, and representability data remain owned by
`CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology`; this leaf only specializes that
API to `SheafOfModules.CommAlg.Modules`.
-/

@[expose] public section

noncomputable section

universe r u v w z g

open CategoryTheory
open CategoryTheory.CochainComplex
open scoped SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.Derived.RHom.Cohomology

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

section DerivedHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has O]

/-- Degree-`n` derived `RHom` cohomology for `O`-module sheaves. -/
@[stacks 0CS6 "CommAlg derived Hom cohomology bifunctor"]
noncomputable abbrev functor (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.functor
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

end DerivedHom

/-- The shifted-Hom target for cohomology of derived `O`-module sheaves. -/
@[stacks 0CS6 "CommAlg shifted derived Hom target"]
noncomputable abbrev shiftedFunctor (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.shiftedFunctor
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

section Representation

variable [IsGrothendieckAbelian.{g}
  (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)]
variable [SheafOfModules.CommAlg.Derived.RHom.Has O]

/-- Derived `RHom` cohomology is represented by shifted morphisms in the derived category. -/
@[stacks 0CS6 "CommAlg derived Hom cohomology representation"]
noncomputable abbrev iso (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.iso
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

/-- The pointwise `R`-linear equivalence from derived-Hom cohomology to shifted Hom. -/
@[stacks 0CS6 "CommAlg derived Hom cohomology as shifted Hom"]
noncomputable abbrev linearEquiv
    (M N : DerivedCategory
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)) (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.linearEquiv
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) M N n

end Representation

section Model

/-- The full subcategory of K-injective complexes used as a concrete `RHom` model. -/
@[stacks 0CS6 "CommAlg K-injective derived Hom model category"]
abbrev Model :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.Model
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)

/-- The product quasi-isomorphism system on the K-injective model category. -/
@[stacks 0CS6 "CommAlg K-injective derived Hom denominators"]
abbrev modelQis :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelQis
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)

/-- The inclusion of K-injective models into the enriched homotopy category. -/
@[stacks 0CS6 "CommAlg K-injective model inclusion"]
abbrev modelInclusion :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelInclusion
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)

/-- The localization of K-injective models into the derived category. -/
@[stacks 0CS6 "CommAlg K-injective model localization"]
noncomputable abbrev modelLocalization :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelLocalization
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)

/-- The strict enriched-Hom model restricted to K-injective pairs. -/
@[stacks 0CS6 "CommAlg strict Hom model on K-injectives"]
noncomputable abbrev modelHom :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelHom
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)

/-- Degree-`n` cohomology of the strict K-injective Hom model. -/
@[stacks 0CS6 "CommAlg strict Hom cohomology model"]
noncomputable abbrev modelCohomology (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelCohomology
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

/-- The shifted-Hom model on K-injective pairs. -/
@[stacks 0CS6 "CommAlg shifted Hom model on K-injectives"]
noncomputable abbrev modelShifted (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelShifted
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

/-- The pointwise linear equivalence from strict model cohomology to shifted Hom. -/
@[stacks 0CS6 "CommAlg K-injective cohomology equivalence"]
noncomputable abbrev modelLinearEquiv
    (X :
      (CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.Model
        (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O))ᵒᵖ ×
      CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.Model
        (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O)) (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelLinearEquiv
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) X n

section DerivedHom

variable [SheafOfModules.CommAlg.Derived.RHom.Has O]

/-- The comparison from derived-Hom cohomology to its strict K-injective model. -/
@[stacks 0CS6 "CommAlg K-injective cohomology comparison"]
noncomputable abbrev modelCohomologyIso (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelCohomologyIso
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

/-- The strict K-injective cohomology-to-shifted-Hom isomorphism. -/
@[stacks 0CS6 "CommAlg K-injective shifted Hom isomorphism"]
noncomputable abbrev modelIso (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelIso
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

/-- The derived-category comparison from cohomology to shifted Hom. -/
@[stacks 0CS6 "CommAlg derived cohomology comparison isomorphism"]
noncomputable abbrev modelComparisonIso (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.Over.RHom.Cohomology.modelComparisonIso
    (R := R) (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) n

end DerivedHom

end Model

end SheafOfModules.CommAlg.Derived.RHom.Cohomology
