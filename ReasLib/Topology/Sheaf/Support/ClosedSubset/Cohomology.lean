/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.GlobalSections
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology with support in a closed subset

This file owns the right-derived functors of global sections with support in a closed subset.
It also provides their objectwise values, functorial maps, cohomological-dimension predicate, and
computation by an injective resolution.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport

variable {X : TopCat.{u}} {Z : Set X}

/-- The degree-`q` right-derived functor of global sections with support in the closed subset `Z`. -/
@[stacks 0A39 "degreewise cohomology-with-support functor"]
noncomputable abbrev functorH (hZ : IsClosed Z) (q : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (functor hZ).rightDerived q

/-- The degree-`q` cohomology of `F` with support in the closed subset `Z`. -/
@[stacks 0A39 "cohomology with support"]
noncomputable abbrev H (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u})
    (q : ℕ) : AddCommGrpCat.{u} :=
  (functorH hZ q).obj F

namespace H

/-- The map on cohomology with support induced by a morphism of sheaves of abelian groups. -/
@[stacks 0A39 "map on cohomology with support"]
noncomputable abbrev map (hZ : IsClosed Z) {F G : X.Sheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) (q : ℕ) : H hZ F q ⟶ H hZ G q :=
  (functorH hZ q).map f

/-- A chosen injective resolution computes cohomology with support by the homology of the
global-sections-with-support complex. -/
@[stacks 0A39 "injective-resolution computation"]
noncomputable abbrev isoHomology (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u})
    (I : InjectiveResolution F) (q : ℕ) :
    H hZ F q ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q).obj
        (((functor hZ).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (functor hZ) q

end H

/-- Global sections with support in `Z` have cohomological dimension at most `d`. -/
@[stacks 0A39 "cohomological dimension with support"]
abbrev HasDimensionLE (hZ : IsClosed Z) (d : ℤ) : Prop :=
  (functor hZ).HasCohomologicalDimensionLE d

/-- Cohomological dimension with support is equivalent to objectwise vanishing above the bound. -/
@[stacks 0A39 "objectwise cohomological-dimension criterion"]
theorem hasDimensionLE_iff (hZ : IsClosed Z) (d : ℤ) :
    HasDimensionLE hZ d ↔
      ∀ q : ℕ, d < (q : ℤ) →
        ∀ F : X.Sheaf AddCommGrpCat.{u}, IsZero (H hZ F q) := sorry

end TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport
