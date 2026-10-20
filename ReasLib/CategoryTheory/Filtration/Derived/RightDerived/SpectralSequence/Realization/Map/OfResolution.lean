/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.OfResolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of unbounded right-derived realizations from explicit data

This leaf packages a resolution map together with its comparison compatibility and association
morphism.  The association morphism remains explicit because it is genuine mathematical data.
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

namespace SpectralSequence.Realization.Map

/- The raw constructor below is useful when the realization records themselves are being built.
For downstream arguments, the existing-realization constructor is the shorter interface. -/

/-- Build a right-derived realization map over two already chosen realizations.

This constructor keeps the realization objects at the boundary, so callers do not have to unpack
their resolutions, comparisons, and associated spectral sequences merely to package a map. -/
@[stacks 0BKK "map from a resolution map over chosen right-derived realizations"]
noncomputable def fromResolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    Realization.Map F f S T where
  resolutionMap := m
  comparisonCompatible := hm
  associationMap := a

/-- A compatible resolution map over chosen realizations admits a realization-map package.

The association morphism is propositionally unique for the fixed filtered-model map; this theorem
exposes existence without selecting a public `Classical.choice` witness. -/
@[stacks 0BKK "existence of a realization map from compatible resolution data"]
theorem nonemptyOfResolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison) :
    Nonempty (Realization.Map F f S T) := sorry

/-- Build a realization map from an explicit resolution map, comparison compatibility proof, and
association morphism. -/
@[stacks 0BKK "map from explicit right-derived resolution data"]
noncomputable def ofResolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    Map F f (Realization.ofResolution F R P E) (Realization.ofResolution F S Q E') where
  resolutionMap := m
  comparisonCompatible := hm
  associationMap := a

/-- The resolution-map component of `Map.ofResolutionMap` is its input map. -/
@[simp, stacks 0BKK "resolution component of an explicit right-derived realization map"]
theorem ofResolutionMap_resolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).resolutionMap = m := sorry

/-- The comparison-compatibility component of `Map.ofResolutionMap` is its input proof. -/
@[simp, stacks 0BKK "comparison component of an explicit right-derived realization map"]
theorem ofResolutionMap_comparisonCompatible
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).comparisonCompatible = hm := sorry

/-- The association-map component of `Map.ofResolutionMap` is its input morphism. -/
@[simp, stacks 0BKK "association component of an explicit right-derived realization map"]
theorem ofResolutionMap_associationMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).associationMap = a := sorry

/-- The `fromResolutionMap` constructor retains its resolution-map component. -/
@[simp, stacks 0BKK "resolution component of a chosen-realization map"]
theorem fromResolutionMap_resolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    (fromResolutionMap F S T m hm a).resolutionMap = m := sorry

/-- The `fromResolutionMap` constructor retains its comparison-compatibility proof. -/
@[simp, stacks 0BKK "comparison component of a chosen-realization map"]
theorem fromResolutionMap_comparisonCompatible
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    (fromResolutionMap F S T m hm a).comparisonCompatible = hm := sorry

/-- The `fromResolutionMap` constructor retains its association morphism. -/
@[simp, stacks 0BKK "association component of a chosen-realization map"]
theorem fromResolutionMap_associationMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    (fromResolutionMap F S T m hm a).associationMap = a := sorry

/-- The filtered-model component of `fromResolutionMap` is induced by its input resolution map. -/
@[simp, stacks 0BKK "filtered component of a chosen-realization map"]
theorem fromResolutionMap_filteredMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    (fromResolutionMap F S T m hm a).filteredMap = modelMap F m := sorry

/-- The spectral-sequence component of `fromResolutionMap` is the supplied association map. -/
@[simp, stacks 0BKK "spectral-sequence component of a chosen-realization map"]
theorem fromResolutionMap_sequenceMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    (S : Realization F K) (T : Realization F L)
    (m : KInjectiveResolution.Map f S.resolution T.resolution)
    (hm : Model.Comparison.IsCompatible F m S.comparison T.comparison)
    (a : FilteredComplex.Association.Hom S.association T.association (modelMap F m)) :
    (fromResolutionMap F S T m hm a).sequenceMap = a.hom := sorry

/-- The filtered-model component of `Map.ofResolutionMap` is induced by its input resolution map.
-/
@[simp, stacks 0BKK "filtered component of an explicit right-derived realization map"]
theorem ofResolutionMap_filteredMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).filteredMap = modelMap F m := sorry

/-- The spectral-sequence component of `Map.ofResolutionMap` is the input association morphism.
-/
@[simp, stacks 0BKK "spectral-sequence component of an explicit right-derived realization map"]
theorem ofResolutionMap_sequenceMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).sequenceMap = a.hom := sorry

end SpectralSequence.Realization.Map

end CategoryTheory.FilteredComplex.RightDerived
