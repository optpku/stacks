/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.LowerShriek
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.WeakSerre
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure

/-!
# Derived quasi-coherent modules on small algebraic-stack sites

The lisse-étale and flat-fppf derived quasi-coherent categories are the full
subcategories of the unbounded module derived categories with quasi-coherent
cohomology. Coefficients have universe `u`, while the sites have universe `u + 1`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The unbounded derived category of modules on the lisse-étale site of an
algebraic stack. -/
abbrev ModuleDerivedLisseEtale (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/-- The unbounded derived category of modules on the flat-fppf site of an
algebraic stack. -/
abbrev ModuleDerivedFlatFppf (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X))

/-- Derived category of quasi-coherent modules on the lisse-étale site, as the
full subcategory of complexes whose cohomology sheaves are quasi-coherent. -/
abbrev DerivedQCohLisseEtale (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))

namespace DerivedQCohLisseEtale

/-- The inclusion of `D_QCoh` of the lisse-étale site into the unbounded
derived category of lisse-étale modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCohLisseEtale X ⥤ ModuleDerivedLisseEtale X :=
  (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).ι

end DerivedQCohLisseEtale

/-- Derived category of quasi-coherent modules on the flat-fppf site, as the
full subcategory of complexes whose cohomology sheaves are quasi-coherent. -/
abbrev DerivedQCohFlatFppf (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))

namespace DerivedQCohFlatFppf

/-- The inclusion of `D_QCoh` of the flat-fppf site into the unbounded derived
category of flat-fppf modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCohFlatFppf X ⥤ ModuleDerivedFlatFppf X :=
  (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).ι

end DerivedQCohFlatFppf

end AlgebraicGeometry.AlgebraicStack
