/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.BoundedBelow
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence

/-!
# Finite-filtered derived global sections

This file specializes the bounded-below finite-filtered right-derived spectral-sequence API to
global sections of modules on a ringed space.  The strict filtered-injective resolution remains
part of the realization, so morphisms and independence of choices are available without rebuilding
local instances or choosing anonymous representatives downstream.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Finite

/-- The bounded-below complex underlying the `p`-th graded piece of a finite filtered complex of
`𝒪_X`-modules. -/
@[stacks 0BKL "graded piece of a bounded-below finite filtered complex"]
noncomputable abbrev gradedPieceComplex (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) (p : ℤ) :
    CochainComplex.Plus X.Modules :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.gradedPieceComplex K p

/-- The bounded-below complex obtained by forgetting the finite filtration. -/
@[stacks 0BKL "underlying bounded-below complex of a finite filtered complex"]
noncomputable abbrev underlyingComplex (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) :
    CochainComplex.Plus X.Modules :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.underlyingComplex K

/-- The cochain map on graded pieces induced by a map of finite filtered complexes. -/
@[stacks 0BKL "map on a finite filtered graded piece"]
noncomputable abbrev gradedPieceComplexMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} (f : K ⟶ L)
    (p : ℤ) : gradedPieceComplex X K p ⟶ gradedPieceComplex X L p :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.gradedPieceComplexMap f p

/-- The cochain map obtained by forgetting the filtration on a map of finite filtered complexes. -/
@[stacks 0BKL "map on an underlying finite filtered complex"]
noncomputable abbrev underlyingComplexMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} (f : K ⟶ L) :
    underlyingComplex X K ⟶ underlyingComplex X L :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.underlyingComplexMap f

/-- The bounded-below derived global-sections value of the `p`-th graded piece. -/
@[stacks 0BKL "derived global sections of a finite-filtered graded piece"]
noncomputable abbrev gradedPiece (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) (p : ℤ) :
    DerivedCategory.Plus (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.gradedPiece
    (leftExactFunctor X) K p

/-- The bounded-below derived global-sections value after forgetting the finite filtration. -/
@[stacks 0BKL "derived global sections of the underlying complex"]
noncomputable abbrev underlying (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) :
    DerivedCategory.Plus (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.underlying
    (leftExactFunctor X) K

/-- The filtered global-sections model attached to an explicit strict filtered-injective
resolution. -/
@[stacks 0BKL "finite-filtered derived global-sections model"]
noncomputable abbrev model (X : RingedSpace.{u})
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (R : Resolution K) : FilteredComplex (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.model
    (leftExactFunctor X) R

/-- A strict filtered-injective realization of the finite-filtered hypercohomology spectral
sequence. -/
@[stacks 0BKL "finite-filtered hypercohomology spectral-sequence realization"]
abbrev Realization (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization
    (leftExactFunctor X) K

namespace Realization

/-- The concrete filtered global-sections model of a finite-filtered realization. -/
@[stacks 0BKL "finite-filtered global-sections model"]
noncomputable abbrev filtered {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : FilteredComplex (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.filtered S

/-- The spectral sequence of a finite-filtered global-sections realization. -/
@[stacks 0BKL "finite-filtered hypercohomology spectral sequence"]
noncomputable abbrev sequence {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) :
    CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0 :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.sequence S

/-- The first page is the hypercohomology of the original graded-piece complex. -/
@[stacks 0BKL "first page of the finite-filtered hypercohomology spectral sequence"]
noncomputable def pageOneIso {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) (p q : ℤ) :
    (S.sequence.page 1).X (p, q) ≅
      cochainCohomology X (gradedPieceComplex X K p).obj (p + q) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.pageOneIso
      S p q ≪≫
    CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow.pointwiseCochainCohomologyIso
      (moduleGlobalSectionsFunctor X) (gradedPieceComplex X K p) (p + q)

/-- The abutment is the hypercohomology of the original complex after forgetting the finite
filtration. -/
@[stacks 0BKL "abutment of the finite-filtered hypercohomology spectral sequence"]
noncomputable def targetIso {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) (n : ℤ) :
    S.filtered.underlying.homology n ≅
      cochainCohomology X (underlyingComplex X K).obj n :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.targetIso S n ≪≫
    CategoryTheory.Functor.RightDerived.Homotopy.BoundedBelow.pointwiseCochainCohomologyIso
      (moduleGlobalSectionsFunctor X) (underlyingComplex X K) n

/-- A map between finite-filtered hypercohomology realizations. -/
@[stacks 0BKL "map of finite-filtered hypercohomology spectral sequences"]
abbrev Map (X : RingedSpace.{u})
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} (f : K ⟶ L)
    (S : Realization X K) (R : Realization X L) :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map f S R

/-- The filtered-model component of a finite-filtered hypercohomology realization map. -/
@[stacks 0BKL "filtered component of a finite-filtered hypercohomology map"]
noncomputable abbrev Map.filteredMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) :
    S.filtered ⟶ R.filtered :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.filteredMap m

/-- The spectral-sequence component of a finite-filtered hypercohomology realization map. -/
@[stacks 0BKL "spectral-sequence component of a finite-filtered hypercohomology map"]
noncomputable abbrev Map.sequenceMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) :
    S.sequence ⟶ R.sequence :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.sequenceMap m

namespace Map

/-- Maps of finite-filtered hypercohomology realizations are determined by their strict
resolution maps. -/
@[ext, stacks 0BKL "extensionality of finite-filtered hypercohomology maps"]
theorem ext {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} {m n : Map X f S R}
    (h : m.resolutionMap.hom = n.resolutionMap.hom) : m = n := sorry

/-- Naturality of the hypercohomological first-page identification. -/
@[reassoc, stacks 0BKL "naturality of the first hypercohomology page"]
theorem pageOne_hom {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (R.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        cochainCohomologyMap X (gradedPieceComplexMap f p).hom (p + q) := sorry

/-- Naturality of the hypercohomological abutment identification. -/
@[reassoc, stacks 0BKL "naturality of the hypercohomology abutment"]
theorem target_hom {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (R.targetIso n).hom =
      (S.targetIso n).hom ≫
        cochainCohomologyMap X (underlyingComplexMap f).hom n := sorry

/-- The identity map of a finite-filtered hypercohomology realization. -/
@[stacks 0BKL "identity map of a finite-filtered hypercohomology spectral sequence"]
noncomputable abbrev id {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : Map X (𝟙 K) S S :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.id S

/-- The resolution component of the identity realization map is the identity. -/
@[simp, stacks 0BKL "identity finite-filtered hypercohomology map"]
theorem id_resolutionMap {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) :
    (id S).resolutionMap = Resolution.Map.id S.resolution := sorry

/-- The composite of finite-filtered hypercohomology realization maps. -/
@[stacks 0BKL "composition of finite-filtered hypercohomology spectral-sequence maps"]
noncomputable abbrev comp {X : RingedSpace.{u}}
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {R : Realization X L} {U : Realization X M}
    (m : Map X f S R) (n : Map X g R U) : Map X (f ≫ g) S U :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.comp m n

/-- The resolution component of a composite realization map is the composite. -/
@[simp, stacks 0BKL "composition of finite-filtered hypercohomology maps"]
theorem comp_resolutionMap {X : RingedSpace.{u}}
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {R : Realization X L} {U : Realization X M}
    (m : Map X f S R) (n : Map X g R U) :
    (comp m n).resolutionMap = Resolution.Map.comp m.resolutionMap n.resolutionMap := sorry

/-- Reindex a finite-filtered hypercohomology map along equality of source morphisms. -/
@[stacks 0BKL "reindexing finite-filtered hypercohomology spectral-sequence maps"]
noncomputable abbrev reindex {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f g : K ⟶ L}
    {S : Realization X K} {R : Realization X L}
    (h : f = g) (m : Map X f S R) : Map X g S R :=
  CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.reindex h m

/-- Reindexing preserves the strict-resolution component. -/
@[simp, stacks 0BKL "reindexing finite-filtered hypercohomology maps"]
theorem reindex_resolutionMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f g : K ⟶ L}
    {S : Realization X K} {R : Realization X L}
    (h : f = g) (m : Map X f S R) :
    (reindex h m).resolutionMap = Resolution.Map.reindex h m.resolutionMap := sorry

/-- The filtered component of the identity realization map is the identity. -/
@[simp, stacks 0BKL "identity finite-filtered hypercohomology map"]
theorem id_filteredMap {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : (id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity realization map is the identity. -/
@[simp, stacks 0BKL "identity finite-filtered hypercohomology map"]
theorem id_sequenceMap {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : (id S).sequenceMap = 𝟙 S.sequence := sorry

/-- Filtered components respect composition of realization maps. -/
@[simp, stacks 0BKL "composition of finite-filtered hypercohomology maps"]
theorem comp_filteredMap {X : RingedSpace.{u}}
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {R : Realization X L} {U : Realization X M}
    (m : Map X f S R) (n : Map X g R U) :
    (comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- Spectral-sequence components respect composition of realization maps. -/
@[simp, stacks 0BKL "composition of finite-filtered hypercohomology maps"]
theorem comp_sequenceMap {X : RingedSpace.{u}}
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {R : Realization X L} {U : Realization X M}
    (m : Map X f S R) (n : Map X g R U) :
    (comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- Reindexing preserves the filtered-model component. -/
@[simp, stacks 0BKL "reindexing finite-filtered hypercohomology maps"]
theorem reindex_filteredMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f g : K ⟶ L}
    {S : Realization X K} {R : Realization X L}
    (h : f = g) (m : Map X f S R) :
    (reindex h m).filteredMap = m.filteredMap := sorry

/-- Reindexing preserves the spectral-sequence component. -/
@[simp, stacks 0BKL "reindexing finite-filtered hypercohomology maps"]
theorem reindex_sequenceMap {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f g : K ⟶ L}
    {S : Realization X K} {R : Realization X L}
    (h : f = g) (m : Map X f S R) :
    (reindex h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing along reflexivity leaves a hypercohomology realization map unchanged. -/
@[simp, stacks 0BKL "reindexing finite-filtered hypercohomology maps"]
theorem reindex_rfl {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) :
    reindex rfl m = m := sorry

/-- The identity realization map is a left identity after reindexing. -/
@[stacks 0BKL "left identity for finite-filtered hypercohomology maps"]
theorem id_comp {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) :
    reindex (Category.id_comp f) (comp (id S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing. -/
@[stacks 0BKL "right identity for finite-filtered hypercohomology maps"]
theorem comp_id {X : RingedSpace.{u}}
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} {f : K ⟶ L}
    {S : Realization X K} {R : Realization X L} (m : Map X f S R) :
    reindex (Category.comp_id f) (comp m (id R)) = m := sorry

/-- Composition of hypercohomology realization maps is associative after reindexing. -/
@[stacks 0BKL "associativity of finite-filtered hypercohomology maps"]
theorem assoc {X : RingedSpace.{u}}
    {K L M N : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization X K} {R : Realization X L}
    {U : Realization X M} {V : Realization X N}
    (m : Map X f S R) (n : Map X g R U) (k : Map X h U V) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

end Map

/-- Remark 20.29.2 (`0BKL`): a bounded-below complex of finite filtered modules admits a
strict filtered-injective hypercohomology spectral-sequence realization. -/
@[stacks 0BKL]
theorem nonempty (X : RingedSpace.{u})
    (K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)) :
    Nonempty (Realization X K) := sorry

/-- A map of bounded-below finite-filtered complexes admits compatible hypercohomology
realizations. -/
@[stacks 0BKL "functoriality"]
theorem existsMap (X : RingedSpace.{u})
    {K L : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)} (f : K ⟶ L) :
    ∃ (S : Realization X K) (R : Realization X L), Nonempty (Map X f S R) := sorry

/-- The finite-filtered hypercohomology spectral sequence is bounded. -/
@[stacks 0BKL "boundedness"]
theorem isBounded {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : S.sequence.IsBounded := sorry

/-- A finite-filtered realization induces finite filtrations on hypercohomology. -/
@[stacks 0BKL "finite filtration on hypercohomology"]
theorem finite {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) : FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- The finite-filtered spectral sequence converges to derived global sections of the
underlying complex. -/
@[stacks 0BKL "convergence"]
theorem converges {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S : Realization X K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

/-- Any supplied comparison between two finite-filtered hypercohomology realizations is an
isomorphism from the first page onward. -/
@[stacks 0BKL "independence of strict filtered-injective resolution"]
theorem existsIsoFromOne {X : RingedSpace.{u}}
    {K : CochainComplex.Plus (FilteredObject.Finite.category X.Modules)}
    (S R : Realization X K) (h : Nonempty (Map X (𝟙 K) S R)) :
    ∃ m : Map X (𝟙 K) S R, m.sequenceMap.IsIsoFrom 1 zero_le_one := sorry

end Realization

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Finite
