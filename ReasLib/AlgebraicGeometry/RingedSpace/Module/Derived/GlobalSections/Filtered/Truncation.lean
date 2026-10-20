/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation

/-!
# The truncation hypercohomology spectral sequence

This file specializes the generic truncation-filtration right-derived spectral sequence to global
sections of modules on a ringed space.  The filtered resolution and standard renumbering stay in
the generic owner; only the geometric names for the second page and abutment are added here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CochainComplex.CartanEilenbergResolution.SpectralSequence

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Truncation

/-- A realization of the renumbered truncation hypercohomology spectral sequence of `K`. -/
@[stacks 0BKM "truncation hypercohomology spectral sequence"]
abbrev Realization (X : RingedSpace.{u}) (K : DerivedCategory X.Modules) :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization
    (moduleGlobalSectionsFunctor X) K

namespace Realization

/-- The filtered global-sections model before renumbering. -/
noncomputable abbrev filtered {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) :
    FilteredComplex (ModuleCat (globalSectionsRing X)) :=
  S.original.filtered

/-- The associated hypercohomology spectral sequence before renumbering. -/
noncomputable abbrev originalSequence {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) :
    CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0 :=
  S.original.sequence

/-- The displayed hypercohomology spectral sequence beginning at `E₂`. -/
noncomputable abbrev sequence {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) :
    E₂CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.renumberedSequence
    (moduleGlobalSectionsFunctor X) S.original

/-- The `(-j)`-th graded piece is the cohomology module sheaf `H^j(K)` placed in degree `j`. -/
noncomputable abbrev gradedPieceIso {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (j : ℤ) :
    (DerivedCategory.truncationFilteredPreimage K).gradedPiece (-j) ≅
      (CochainComplex.singleFunctor X.Modules j).obj
        ((DerivedCategory.homologyFunctor X.Modules j).obj K) :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.gradedPieceIso
    S j

/-- The second page is sheaf cohomology of the cohomology module sheaves:
`E₂^{i,j} = H^i(X, H^j(K))`. -/
@[stacks 0BKM "second page of the truncation hypercohomology spectral sequence"]
noncomputable abbrev pageTwoIso {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (i : ℕ) (j : ℤ) :
    (S.sequence.page 2).X (Int.ofNat i, j) ≅
      moduleCohomologyAtOpen (⊤ : Opens X.carrier)
        ((DerivedCategory.homologyFunctor X.Modules j).obj K) i :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.pageTwoIso
    S i j

/-- The filtered model abuts to the hypercohomology of `K`. -/
noncomputable abbrev targetIso {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (n : ℤ) :
    S.filtered.underlying.homology n ≅ (GlobalSections.cohomologyFunctor X n).obj K :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.targetIso
    S n

/-- The original sequence is associated to the retained filtered global-sections model. -/
theorem isAssociated {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) :
    CategoryTheory.FilteredComplex.IsAssociated S.filtered S.originalSequence := sorry

/-- The displayed `E₂` sequence is the standard page-and-bidegree renumbering of the original
associated sequence. -/
theorem isRenumbering {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) :
    CohomologicalSpectralSequence.IsRenumbering
      (CohomologicalSpectralSequence.Page.One.ofZero S.originalSequence) S.sequence := sorry

/-- Every derived module on a ringed space admits a truncation hypercohomology realization. -/
@[stacks 0BKM]
theorem nonempty (X : RingedSpace.{u}) (K : DerivedCategory X.Modules) :
    Nonempty (Realization X K) := sorry

/-- On a bounded-below representative, the renumbered truncation sequence compares with the
second Cartan--Eilenberg spectral sequence from `E₂` onward. -/
@[stacks 0BKM "comparison with the second Cartan-Eilenberg spectral sequence"]
theorem cartanEilenbergComparison {X : RingedSpace.{u}}
    (K : CochainComplex.Plus X.Modules) (I : CochainComplex.CartanEilenbergResolution K) :
    Nonempty (Second.RenumberedComparison (moduleGlobalSectionsFunctor X) K I) := sorry

/-- For a bounded-below derived module, the renumbered hypercohomology spectral sequence is
bounded. -/
theorem isBounded {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (hK : DerivedCategory.IsBoundedBelow K) :
    S.sequence.IsBounded := sorry

/-- For a bounded-below derived module, the induced hypercohomology filtrations are finite. -/
theorem finite {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (hK : DerivedCategory.IsBoundedBelow K) :
    CategoryTheory.FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- For a bounded-below derived module, the original hypercohomology sequence converges and the
displayed `E₂` sequence is its standard renumbering. -/
theorem converges {X : RingedSpace.{u}} {K : DerivedCategory X.Modules}
    (S : Realization X K) (hK : DerivedCategory.IsBoundedBelow K) :
    CategoryTheory.FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering
      S.filtered S.originalSequence S.sequence := sorry

end Realization

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Truncation
