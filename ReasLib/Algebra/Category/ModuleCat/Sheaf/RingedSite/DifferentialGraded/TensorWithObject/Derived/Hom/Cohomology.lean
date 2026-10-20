/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.RHom.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.RHom.Cohomology

/-!
# Cohomology comparison for the derived tensor-Hom map

This leaf packages the degreewise natural comparison attached to the derived tensor-Hom
transformation.  The source and target representability isomorphisms are imported from their
independent owners; the only new statement is the canonical comparison square between them.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open SheafOfModules.RingedSite.TensorWithObject
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived.Hom.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- Degree-`n` cohomology of the source derived Hom bifunctor. -/
@[stacks 0CS6 "source cohomology of the derived tensor-Hom comparison"]
noncomputable abbrev sourceFunctor (K : Complex (J := J) (O := O)) (n : ℤ) :=
  Derived.Hom.Source.functor K ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} ℤ) n

/-- Degree-`n` cohomology of global derived Hom after applying derived tensor in both variables. -/
@[stacks 0CS6 "target cohomology of the derived tensor-Hom comparison"]
noncomputable abbrev targetFunctor (K : Complex (J := J) (O := O)) (n : ℤ) :=
  Derived.Hom.Target.functor K ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} ℤ) n

/-- The degree-`n` cohomology natural transformation induced by the derived tensor-Hom map. -/
@[stacks 0CS6 "cohomology natural transformation of the derived tensor-Hom comparison"]
noncomputable def comparison (K : Complex (J := J) (O := O)) (n : ℤ) :
    sourceFunctor K n ⟶ targetFunctor K n :=
  Functor.whiskerRight
    (Derived.Hom.comparison K)
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} ℤ) n)

/-- The degree-`n` cohomology map at a pair of derived DG modules. -/
@[stacks 0CS6 "pointwise cohomology map of the derived tensor-Hom comparison"]
noncomputable abbrev cohomologyMap (K : Complex (J := J) (O := O))
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  (comparison K n).app (Opposite.op M, N)

/-- The source cohomology-to-shifted-Hom linear equivalence. -/
@[stacks 0CS6 "source cohomology representability isomorphism"]
noncomputable abbrev sourceLinearEquiv (K : Complex (J := J) (O := O))
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  DifferentialGradedModule.Derived.RHom.Cohomology.linearEquiv
    (endDGA K) M N n

/-- The target cohomology-to-shifted-Hom linear equivalence after derived tensoring. -/
@[stacks 0CS6 "target cohomology representability isomorphism"]
noncomputable abbrev targetLinearEquiv (K : Complex (J := J) (O := O))
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ) :=
  CategoryTheory.CochainComplex.Enriched.RHom.Cohomology.linearEquiv
    ((Derived.tensorFunctor K).obj M) ((Derived.tensorFunctor K).obj N) n

/-- Naturality of the degree-`n` cohomology comparison in both derived variables. -/
@[reassoc, stacks 0CS6 "naturality of the cohomology comparison"]
theorem comparison_naturality (K : Complex (J := J) (O := O)) (n : ℤ)
    {X Y : (DifferentialGradedModule.Derived.Category (endDGA K))ᵒᵖ ×
      DifferentialGradedModule.Derived.Category (endDGA K)} (f : X ⟶ Y) :
    (sourceFunctor K n).map f ≫ (comparison K n).app Y =
      (comparison K n).app X ≫ (targetFunctor K n).map f := sorry

/-- The degree-`n` comparison is the shifted image of the source cohomology class. -/
@[stacks 0CS6 "cohomology comparison as shifted Hom map"]
theorem cohomologyMap_shiftedHom (K : Complex (J := J) (O := O))
    (M N : DifferentialGradedModule.Derived.Category (endDGA K)) (n : ℤ)
    (x : (sourceFunctor K n).obj (Opposite.op M, N)) :
    targetLinearEquiv K M N n
        (cohomologyMap K M N n x) =
      ShiftedHom.map (sourceLinearEquiv K M N n x) (Derived.tensorFunctor K) := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived.Hom.Cohomology
