/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Topology.Sheaf.Derived.Basic
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive sheaves and closed-support derived functors

This leaf compares derived closed-support constructions for module sheaves with the corresponding
right-derived constructions on their underlying sheaves of additive groups.  A bundled closed
subset owns all closedness data, and the exact derived forgetful functors are named separately so
downstream statements do not rebuild them locally.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_additive
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteLimits
attribute [local instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteColimits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- Forget an ambient derived module to its underlying derived additive sheaf. -/
@[stacks 0G74 "underlying additive sheaf of a derived module"]
abbrev ambientForget :
    AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
      DerivedCategory (X.carrier.Sheaf AddCommGrpCat.{u}) :=
  (moduleUnderlyingSheaf X).mapDerivedCategory

/-- Forget a derived module on `Z` to its underlying derived additive sheaf on `Z`. -/
@[stacks 0G74 "underlying additive sheaf of a closed-subset derived module"]
abbrev closedForget :
    ModuleDerived X Z ⥤
      DerivedCategory ((TopCat.of (Z : Set X)).Sheaf AddCommGrpCat.{u}) :=
  (closedSubsetModuleUnderlyingSheaf X (Z : Set X)).mapDerivedCategory

/-- Module-valued derived sections with support, followed by forgetting the module structure. -/
@[stacks 0G74 "underlying additive derived sections with support"]
abbrev moduleLocalCohomology :
    AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
      DerivedCategory ((TopCat.of (Z : Set X)).Sheaf AddCommGrpCat.{u}) :=
  SectionsWithSupport.derived X Z ⋙ closedForget X Z

/-- Derived sections with support of the underlying additive sheaf. -/
@[stacks 0G74 "additive derived sections with support"]
abbrev abelianLocalCohomology :
    AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤
      DerivedCategory ((TopCat.of (Z : Set X)).Sheaf AddCommGrpCat.{u}) :=
  ambientForget X ⋙ Functor.RightDerived.Cochain.functor
    (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor Z.isClosed)

/-- Forgetting module structure commutes with derived sections with support, at the functor
level. -/
@[stacks 0G74 "underlying additive comparison for derived sections with support"]
theorem localCohomology_isomorphic :
    IsIsomorphic (moduleLocalCohomology X Z) (abelianLocalCohomology X Z) := sorry

/-- Forgetting module structure commutes with derived sections with support at every ambient
derived module. -/
@[stacks 0G74 "underlying additive comparison for derived sections with support"]
theorem localCohomology_obj_isomorphic
    (K : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    IsIsomorphic
      ((moduleLocalCohomology X Z).obj K)
      ((abelianLocalCohomology X Z).obj K) := sorry

/-- Module-valued derived global sections with support, followed by forgetting the coefficient
module structure. -/
@[stacks 0G74 "underlying additive derived global sections with support"]
abbrev moduleGlobalSections :
    AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u} :=
  GlobalSectionsWithSupport.derived X Z ⋙
    ModuleCat.forgetDerived (globalSectionsRing X)

/-- Derived global sections with support of the underlying additive sheaf. -/
@[stacks 0G74 "additive derived global sections with support"]
abbrev abelianGlobalSections :
    AlgebraicGeometry.RingedSpace.ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{u} :=
  ambientForget X ⋙ Functor.RightDerived.Cochain.functor
    (TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport.functor Z.isClosed)

/-- Forgetting module structure commutes with derived global sections with support, at the
functor level. -/
@[stacks 0G74 "underlying additive comparison for derived global sections with support"]
theorem globalSections_isomorphic :
    IsIsomorphic (moduleGlobalSections X Z) (abelianGlobalSections X Z) := sorry

/-- Forgetting module structure commutes with derived global sections with support at every
ambient derived module. -/
@[stacks 0G74 "underlying additive comparison for derived global sections with support"]
theorem globalSections_obj_isomorphic
    (K : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    IsIsomorphic
      ((moduleGlobalSections X Z).obj K)
      ((abelianGlobalSections X Z).obj K) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying
