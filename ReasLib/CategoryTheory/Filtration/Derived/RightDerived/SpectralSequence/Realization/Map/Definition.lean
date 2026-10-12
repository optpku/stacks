/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Views
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of unbounded filtered right-derived realizations

A realization map retains the resolution morphism, model-comparison compatibility, and associated spectral-sequence morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization

/-- A map of right-derived spectral-sequence realizations.  Its spectral-sequence component is
tied to a morphism of resolutions and to the canonical model comparisons. -/
@[stacks 0BKK "map of unbounded filtered right-derived spectral sequences"]
structure Map {K L : FilteredComplex A} (f : K ⟶ L)
    (S : Realization F K) (T : Realization F L) where
  /-- The morphism between the chosen filtered K-injective resolutions. -/
  resolutionMap : KInjectiveResolution.Map f S.resolution T.resolution
  /-- Naturality of the model cohomology comparisons. -/
  comparisonCompatible :
    Model.Comparison.IsCompatible F resolutionMap S.comparison T.comparison
  /-- The compatible map of the associated spectral sequences. -/
  associationMap : FilteredComplex.Association.Hom
    S.association T.association (modelMap F resolutionMap)

/-- The filtered-model component of a map of right-derived realizations. -/
@[stacks 0BKK "filtered component of a right-derived realization map"]
noncomputable abbrev Map.filteredMap {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    S.filtered ⟶ T.filtered :=
  modelMap F m.resolutionMap

/-- The spectral-sequence component of a map of right-derived realizations. -/
@[stacks 0BKK "spectral-sequence component of a right-derived realization map"]
noncomputable abbrev Map.sequenceMap {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    S.sequence ⟶ T.sequence :=
  m.associationMap.hom

/-- The association morphism underlying a right-derived realization map.  This neutral view
matches the generic filtered-realization interface and avoids exposing the structure field used
to construct the map. -/
@[stacks 0BKK "association morphism of a filtered right-derived realization map"]
noncomputable abbrev Map.toAssociationHom {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  m.associationMap

/-- The association morphism underlying a right-derived realization map has the same
spectral-sequence component as the realization map. -/
@[simp, stacks 0BKK "spectral-sequence component of a filtered right-derived association map"]
theorem Map.toAssociationHom_hom {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    m.toAssociationHom.hom = m.sequenceMap := sorry

/-- Maps of right-derived realizations are determined by their morphisms between the chosen
filtered K-injective resolutions. -/
@[ext, stacks 0BKK "extensionality of maps of filtered right-derived spectral sequences"]
theorem Map.ext {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Map F f S T}
    (h : m.resolutionMap.hom = n.resolutionMap.hom) : m = n := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived

