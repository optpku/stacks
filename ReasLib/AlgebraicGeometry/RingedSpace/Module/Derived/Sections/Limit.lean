module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived limits of open sections

This leaf is the ringed-space specialization of the sequential derived-limit API.  The ordinary
open-section functor and its underlying additive functor are the canonical owners; countable-limit
preservation is installed once here so later statements do not rebuild local instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Sections.Limit

variable (X : RingedSpace.{u}) (U : Opens X.carrier)

/-- The module-valued open-section functor, named at the derived-limit layer. -/
@[stacks 0D60 "module-valued open sections functor"]
abbrev sectionsFunctor : X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  moduleSectionsEvaluationFunctor X U

/-- Evaluation on an open preserves countable products. -/
@[stacks 0D60 "open sections preserve countable products", instance]
noncomputable instance sectionsFunctor_preservesDiscreteNatLimits :
    PreservesLimitsOfShape (Discrete ℕ) (sectionsFunctor X U) := sorry

/-- The underlying additive open-section functor, named at the derived-limit layer. -/
@[stacks 0D60 "underlying additive open sections functor"]
abbrev underlyingFunctor : X.Modules ⥤ AddCommGrpCat.{u} :=
  moduleSectionsAsAbelianFunctor X U

/-- The underlying additive open-section functor preserves countable products. -/
@[stacks 0D60 "underlying open sections preserve countable products", instance]
noncomputable instance underlyingFunctor_preservesDiscreteNatLimits :
    PreservesLimitsOfShape (Discrete ℕ) (underlyingFunctor X U) := sorry

/-- The module-valued derived open-section functor carries a sequential derived limit to the
derived limit of the stagewise sections. -/
@[stacks 0D60 "derived open sections preserve sequential limits"]
theorem preservesDerivedLimit
    [IsGrothendieckAbelian X.Modules]
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    Nonempty (IsDerivedLimit
      (Ksys ⋙ moduleDerivedSectionsAtOpen X U)
      ((moduleDerivedSectionsAtOpen X U).obj K)) := sorry

/-- The underlying additive derived open-section functor carries a sequential derived limit to the
derived limit of the stagewise sections. -/
@[stacks 0D60 "underlying derived open sections preserve sequential limits"]
theorem underlyingPreservesDerivedLimit
    [IsGrothendieckAbelian X.Modules]
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    Nonempty (IsDerivedLimit
      (Ksys ⋙ moduleDerivedSectionsAtOpenToAb X U)
      ((moduleDerivedSectionsAtOpenToAb X U).obj K)) := sorry

/-- Forgetting section scalars identifies open hypercohomology with additive derived homology. -/
@[stacks 0D60 "open hypercohomology homology identification"]
noncomputable abbrev hypercohomologyIso
    [IsGrothendieckAbelian X.Modules] (K : ModuleDerived X) (m : ℤ) :
    moduleOpenHypercohomology X U K m ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
        ((moduleDerivedSectionsAtOpenToAb X U).obj K) :=
  CategoryTheory.exactFunctor_homology_iso_mapDerivedCategory
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u})
    ((moduleDerivedSectionsAtOpen X U).obj K) m

/-- The Milnor short exact sequence for open hypercohomology, expressed using the canonical
underlying derived-section tower. -/
@[stacks 0D60 "open hypercohomology Milnor short exact sequence", stacks 0BKR
  "20.37.3.1: Milnor short exact sequence for open hypercohomology"]
theorem cohomologyShortExact
    [IsGrothendieckAbelian X.Modules]
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (K : ModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
            ((Ksys ⋙ moduleDerivedSectionsAtOpenToAb X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)) ⟶
          moduleOpenHypercohomology X U K m)
      (π :
        moduleOpenHypercohomology X U K m ⟶
          limit ((Ksys ⋙ moduleDerivedSectionsAtOpenToAb X U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Sections.Limit

end
