/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Minus

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsNoetherian X]
variable [HasDerivedCategory.{w} (SheafOfModules X.ringCatSheaf)]
variable [HasDerivedCategory.{w}
  (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory]

open DerivedCategory.Minus.CohomologyIn in
/-- For a Noetherian scheme, the canonical bounded-above comparison from coherent module
sheaves to complexes with coherent cohomology is an equivalence. -/
theorem coherentMinusComparisonIsEquivalence :
    Functor.IsEquivalence
      (Comparison.functor (SheafOfModules.isCoherent X.ringCatSheaf)) := sorry

open DerivedCategory.Bounded.CohomologyIn in
/-- For a Noetherian scheme, the canonical bounded comparison from coherent module sheaves to
complexes with coherent cohomology is an equivalence. -/
theorem coherentBoundedComparisonIsEquivalence :
    Functor.IsEquivalence
      (Comparison.functor (SheafOfModules.isCoherent X.ringCatSheaf)) := sorry

end AlgebraicGeometry.Scheme
