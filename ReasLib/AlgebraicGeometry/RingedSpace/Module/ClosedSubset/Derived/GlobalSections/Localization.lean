/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization triangles for derived global sections with support

For a bundled closed subset `Z` of a ringed space, this file owns the localization triangle whose
third term is derived sections on the open complement, viewed over the ambient global section
ring. The boundary is exposed through a predicate because its existence, rather than a chosen
representative, is the mathematical content.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- Derived sections on the open complement of `Z`, with scalars restricted to `Γ(X, 𝒪_X)`. -/
@[stacks 0G71 "derived sections on the complement of a closed subset"]
abbrev openTerm :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.Sections.OverGlobal.derived X Z.compl

/-- Derived global sections with support, shifted by one. -/
@[stacks 0G71 "shifted derived global sections with support"]
abbrev shifted :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  GlobalSectionsWithSupport.derived X Z ⋙
    shiftFunctor (DerivedCategory (ModuleCat (globalSectionsRing X))) (1 : ℤ)

/-- The functorial localization triangle determined by a boundary morphism. -/
@[stacks 0G71 "functorial localization triangle for derived global sections with support"]
abbrev triangleFunctor (δ : openTerm X Z ⟶ shifted X Z) :
    DerivedCategory X.Modules ⥤
      Triangle (DerivedCategory (ModuleCat (globalSectionsRing X))) :=
  Triangle.functorMk
    (GlobalSectionsWithSupport.forgetDerived X Z)
    (Module.Derived.Sections.OverGlobal.derivedRestriction X Z.compl)
    δ

/-- A natural transformation is a localization boundary when its components complete the
forget-support and restriction maps to distinguished triangles. -/
@[stacks 0G71 "localization boundary for derived global sections with support"]
def IsBoundary (δ : openTerm X Z ⟶ shifted X Z) : Prop :=
  ∀ K : DerivedCategory X.Modules,
    (triangleFunctor X Z δ).obj K ∈
      distTriang (DerivedCategory (ModuleCat (globalSectionsRing X)))

/-- A functorial localization boundary exists for derived global sections with support. -/
@[stacks 0G71 "localization triangle for derived global sections with support"]
theorem exists_boundary :
    ∃ δ : openTerm X Z ⟶ shifted X Z, IsBoundary X Z δ := sorry

/-- Objectwise localization triangle for derived global sections with support. -/
@[stacks 0G71 "objectwise localization triangle for derived global sections with support"]
theorem triangle (K : DerivedCategory X.Modules) :
    ∃ δ : (openTerm X Z).obj K ⟶
        ((GlobalSectionsWithSupport.derived X Z).obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((GlobalSectionsWithSupport.forgetDerived X Z).app K)
          ((Module.Derived.Sections.OverGlobal.derivedRestriction X Z.compl).app K)
          δ ∈
        distTriang (DerivedCategory (ModuleCat (globalSectionsRing X))) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.Localization
