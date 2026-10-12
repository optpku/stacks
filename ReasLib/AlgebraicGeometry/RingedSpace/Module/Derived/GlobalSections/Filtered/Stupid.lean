/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid

/-!
# The stupid-filtration hypercohomology spectral sequence

This file specializes the generic stupid-filtration right-derived realization to module-valued
global sections on a ringed space.  The first page is expressed using the canonical sheaf
cohomology owner rather than an ad hoc shifted-complex formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CochainComplex.CartanEilenbergResolution.SpectralSequence

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Stupid

/-- A realization of the stupid-filtration hypercohomology spectral sequence of `K`. -/
@[stacks 0FLK "stupid-filtration hypercohomology spectral sequence"]
abbrev Realization (X : RingedSpace.{u}) (K : CochainComplex X.Modules ℤ) :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization
    (moduleGlobalSectionsFunctor X) K

namespace Realization

/-- The filtered global-sections model of the stupid filtration. -/
noncomputable abbrev filtered {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) :
    FilteredComplex (ModuleCat (globalSectionsRing X)) :=
  S.original.filtered

/-- The associated stupid-filtration hypercohomology spectral sequence. -/
noncomputable abbrev sequence {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) :
    CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0 :=
  S.original.sequence

/-- The `p`-th graded piece is `K^p` placed in cohomological degree `p`. -/
noncomputable abbrev gradedPieceIso {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) (p : ℤ) :
    K.stupidFiltration.gradedPiece p ≅
      (CochainComplex.singleFunctor X.Modules p).obj (K.X p) :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.gradedPieceIso
    S p

/-- The first page is the sheaf cohomology of the terms: `E₁^{p,q} = H^q(X, K^p)`. -/
@[stacks 0FLK "first page of the stupid-filtration hypercohomology spectral sequence"]
noncomputable abbrev pageOneIso {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) (p : ℤ) (q : ℕ) :
    (S.sequence.page 1).X (p, Int.ofNat q) ≅
      moduleCohomologyAtOpen (⊤ : Opens X.carrier) (K.X p) q :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.pageOneIso
    S p q

/-- The map on the first page induced by the differential `K^p ⟶ K^{p+1}`. -/
noncomputable abbrev pageOneMap {X : RingedSpace.{u}} (K : CochainComplex X.Modules ℤ)
    (p : ℤ) (q : ℕ) :
    moduleCohomologyAtOpen (⊤ : Opens X.carrier) (K.X p) q ⟶
      moduleCohomologyAtOpen (⊤ : Opens X.carrier) (K.X (p + 1)) q :=
  (moduleCohomologyAtOpenFunctor X ⊤ q).map (K.d p (p + 1))

/-- The first-page differential is induced by the differential of `K`. -/
theorem pageOneCommSq {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) (p : ℤ) (q : ℕ) :
    CommSq
      ((S.sequence.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
      (pageOneIso S p q).hom
      (pageOneIso S (p + 1) q).hom
      (pageOneMap K p q) := sorry

/-- The first page vanishes in negative cohomological rows. -/
theorem pageOneIsZero {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) (p q : ℤ) (hq : q < 0) :
    IsZero ((S.sequence.page 1).X (p, q)) := sorry

/-- The filtered model abuts to the hypercohomology of the source complex. -/
noncomputable abbrev targetIso {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) (n : ℤ) :
    S.filtered.underlying.homology n ≅ GlobalSections.cochainCohomology X K n :=
  CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.targetIso
    S n

/-- The selected sequence is associated to the filtered global-sections model. -/
theorem isAssociated {X : RingedSpace.{u}} {K : CochainComplex X.Modules ℤ}
    (S : Realization X K) :
    CategoryTheory.FilteredComplex.IsAssociated S.filtered S.sequence := sorry

/-- Every complex of modules on a ringed space admits a stupid-filtration hypercohomology
realization. -/
@[stacks 0FLK]
theorem nonempty (X : RingedSpace.{u}) (K : CochainComplex X.Modules ℤ) :
    Nonempty (Realization X K) := sorry

/-- The stupid-filtration hypercohomology sequence compares with the first
Cartan--Eilenberg spectral sequence from `E₁` onward. -/
@[stacks 0FLK "comparison with the first Cartan-Eilenberg spectral sequence"]
theorem cartanEilenbergComparison {X : RingedSpace.{u}}
    (K : CochainComplex.Plus X.Modules) (I : CochainComplex.CartanEilenbergResolution K) :
    Nonempty (First.UnboundedComparison (moduleGlobalSectionsFunctor X) K I) := sorry

/-- For a bounded-below complex, the stupid-filtration hypercohomology sequence is bounded. -/
theorem isBounded {X : RingedSpace.{u}} (K : CochainComplex.Plus X.Modules)
    (S : Realization X K.obj) : S.sequence.IsBounded := sorry

/-- For a bounded-below complex, the induced hypercohomology filtrations are finite. -/
theorem finite {X : RingedSpace.{u}} (K : CochainComplex.Plus X.Modules)
    (S : Realization X K.obj) :
    CategoryTheory.FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- For a bounded-below complex, the stupid-filtration hypercohomology sequence converges. -/
theorem converges {X : RingedSpace.{u}} (K : CochainComplex.Plus X.Modules)
    (S : Realization X K.obj) :
    CategoryTheory.FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end Realization

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Stupid
