/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Displayed
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport

/-!
# The Total Category of Grothendieck Spectral-Sequence Realizations

Grothendieck spectral-sequence realizations form the total category of their displayed family
over the bounded-below derived category.  This file keeps the Grothendieck names for the
realization and map components while reusing the generic displayed-total category, its base
projection, and its equality transport.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

/-- The total category of Grothendieck spectral-sequence realizations over varying bounded-below
derived objects. -/
@[stacks 015N "total category of Grothendieck spectral-sequence realizations"]
abbrev Total
    (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) :=
  DisplayedCategory.Total (displayedCategory G RF RGF)

namespace Total

variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}

/-- The Grothendieck spectral-sequence realization stored by a total object. -/
@[stacks 015N "Grothendieck realization of a total spectral-sequence object"]
abbrev realization (S : Total G RF RGF) : SpectralSequence G RF RGF S.base := S.obj

namespace Hom

/-- The Grothendieck spectral-sequence map stored by a total morphism. -/
@[stacks 015N "Grothendieck map of a total spectral-sequence morphism"]
abbrev map {S T : Total G RF RGF} (f : S ⟶ T) :
    SpectralSequence.Map f.base S.realization T.realization :=
  f.displayed

/-- Transport a total Grothendieck morphism along an equality of its base arrows. -/
@[stacks 015N "reindexing total Grothendieck spectral-sequence morphisms"]
abbrev reindex {S T : Total G RF RGF} {f : S ⟶ T} {g : S.base ⟶ T.base}
    (h : f.base = g) : S ⟶ T :=
  DisplayedCategory.Total.Hom.reindex (f := f) h

/-- The Grothendieck map of a reindexed total morphism is the owner-level reindexed map. -/
@[simp, stacks 015N "map of a reindexed total Grothendieck spectral-sequence morphism"]
theorem reindex_map {S T : Total G RF RGF} {f : S ⟶ T} {g : S.base ⟶ T.base}
    (h : f.base = g) :
    (reindex h).map = SpectralSequence.Map.reindex h f.map := sorry

/-- Two total Grothendieck morphisms are equal when their base arrows and reindexed realization
maps agree. -/
@[ext (iff := false), stacks 015N "extensionality of total Grothendieck spectral-sequence morphisms"]
theorem ext_reindex {S T : Total G RF RGF} {f g : S ⟶ T}
    (h_base : f.base = g.base)
    (h_map : SpectralSequence.Map.reindex h_base f.map = g.map) : f = g := sorry

/-- A Grothendieck total morphism is equal exactly when its reindexed realization maps agree. -/
@[simp, stacks 015N "reindexed extensionality criterion for total Grothendieck maps"]
theorem ext_reindex_iff {S T : Total G RF RGF} {f g : S ⟶ T}
    (h_base : f.base = g.base) :
    f = g ↔ SpectralSequence.Map.reindex h_base f.map = g.map := sorry

/-- A total Grothendieck morphism is determined by its base arrow and its underlying neutral
realization map. -/
@[stacks 015N "extensionality of total Grothendieck spectral-sequence morphisms"]
theorem ext_toMap {S T : Total G RF RGF} {f g : S ⟶ T}
    (h_base : f.base = g.base) (h_map : f.map.toMap = g.map.toMap) : f = g := sorry

end Hom

/-- The functorial-abutment realization underlying a total Grothendieck spectral sequence. -/
@[stacks 015N "functorial-abutment projection from total Grothendieck spectral sequences"]
abbrev toWithAbutment (S : Total G RF RGF) :
    FilteredComplex.SpectralSequence.Realization.WithAbutment
      (abutmentFunctor RGF) S.base :=
  S.realization.toWithAbutment

namespace Hom

/-- The generic functorial-abutment map underlying a total Grothendieck morphism. -/
@[stacks 015N "functorial-abutment map of total Grothendieck spectral sequences"]
abbrev toWithAbutmentMap {S T : Total G RF RGF} (f : S ⟶ T) :
    FilteredComplex.SpectralSequence.Realization.WithAbutment.Map
      (abutmentFunctor RGF) f.base S.toWithAbutment T.toWithAbutment :=
  f.map.toWithAbutmentMap

/-- A total Grothendieck morphism is determined by its base arrow and generic functorial-abutment
map after canonical transport. -/
@[stacks 015N "generic extensionality of total Grothendieck spectral-sequence morphisms"]
theorem ext_toWithAbutmentMap {S T : Total G RF RGF} {f g : S ⟶ T}
    (h_base : f.base = g.base)
    (h_map :
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.reindex
          (abutmentFunctor RGF) h_base (Hom.toWithAbutmentMap f) =
        Hom.toWithAbutmentMap g) : f = g := sorry

/-- Reindexing a total morphism agrees with the neutral functorial-abutment reindexing. -/
@[simp, stacks 015N "reindexing total morphisms in the abutment view"]
theorem reindex_toWithAbutmentMap {S T : Total G RF RGF} {f : S ⟶ T}
    {g : S.base ⟶ T.base} (h : f.base = g) :
    Hom.toWithAbutmentMap (reindex h) =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.reindex
        (abutmentFunctor RGF) h (Hom.toWithAbutmentMap f) := sorry

/-- Reindexing leaves the underlying neutral realization map unchanged. -/
@[simp, stacks 015N "reindexing total morphisms in the neutral view"]
theorem reindex_toMap {S T : Total G RF RGF} {f : S ⟶ T} {g : S.base ⟶ T.base}
    (h : f.base = g) : (reindex h).map.toMap = f.map.toMap := sorry

/-- Reindexing leaves the filtered-complex component of a total morphism unchanged. -/
@[simp, stacks 015N "reindexing total filtered maps"]
theorem reindex_filteredMap {S T : Total G RF RGF} {f : S ⟶ T}
    {g : S.base ⟶ T.base} (h : f.base = g) :
    (reindex h).map.filteredMap = f.map.filteredMap := sorry

/-- Reindexing leaves the spectral-sequence component of a total morphism unchanged. -/
@[simp, stacks 015N "reindexing total spectral-sequence maps"]
theorem reindex_sequenceMap {S T : Total G RF RGF} {f : S ⟶ T}
    {g : S.base ⟶ T.base} (h : f.base = g) :
    (reindex h).map.sequenceMap = f.map.sequenceMap := sorry

/-- Reindexing leaves the association morphism unchanged after transporting its filtered-map
index. -/
@[simp, stacks 015N "reindexing total association morphisms"]
theorem toAssociationHom_reindex {S T : Total G RF RGF} {f : S ⟶ T}
    {g : S.base ⟶ T.base} (h : f.base = g) :
    ((reindex_filteredMap h) ▸ (reindex h).map.toAssociationHom) =
      f.map.toAssociationHom := sorry

end Hom

/-- The Grothendieck map stored by a total identity is the owner-level identity map. -/
@[simp, stacks 015N "realization component of a total Grothendieck spectral-sequence identity"]
theorem id_map (S : Total G RF RGF) :
    (𝟙 S : S ⟶ S).map = SpectralSequence.Map.id S.realization := sorry

/-- The Grothendieck map stored by a total composite is the owner-level composite map. -/
@[simp, stacks 015N "realization component of total Grothendieck spectral-sequence composition"]
theorem comp_map {S T U : Total G RF RGF} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).map = SpectralSequence.Map.comp f.map g.map := sorry

/-- The generic functorial-abutment map underlying a total identity. -/
@[simp, stacks 015N "functorial-abutment map of a total identity"]
theorem id_toWithAbutmentMap (S : Total G RF RGF) :
    Hom.toWithAbutmentMap (𝟙 S : S ⟶ S) =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.id
        (abutmentFunctor RGF) S.toWithAbutment := sorry

/-- The generic functorial-abutment map underlying a total composite. -/
@[simp, stacks 015N "functorial-abutment map of a total composite"]
theorem comp_toWithAbutmentMap {S T U : Total G RF RGF} (f : S ⟶ T) (g : T ⟶ U) :
    Hom.toWithAbutmentMap (f ≫ g) =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.comp
        (abutmentFunctor RGF) (Hom.toWithAbutmentMap f) (Hom.toWithAbutmentMap g) := sorry

/-- Forget a total Grothendieck spectral-sequence realization to its bounded-below derived base. -/
@[stacks 015N "base functor from total Grothendieck spectral-sequence realizations"]
abbrev forgetBase : Total G RF RGF ⥤ DerivedCategory.Plus A :=
  DisplayedCategory.Total.forget (displayedCategory G RF RGF)

/-- The object map of `forgetBase` returns the supporting derived object. -/
@[simp, stacks 015N "base functor from total Grothendieck spectral-sequence realizations"]
theorem forgetBase_obj (S : Total G RF RGF) : forgetBase.obj S = S.base := sorry

/-- The morphism map of `forgetBase` returns the underlying derived-category arrow. -/
@[simp, stacks 015N "base functor from total Grothendieck spectral-sequence realizations"]
theorem forgetBase_map {S T : Total G RF RGF} (f : S ⟶ T) :
    forgetBase.map f = f.base := sorry

/-- The neutral realization map underlying a total identity is the identity. -/
@[simp, stacks 015N "neutral realization map of a total identity"]
theorem id_toMap (S : Total G RF RGF) :
    (𝟙 S : S ⟶ S).map.toMap =
      FilteredComplex.SpectralSequence.Realization.Map.id S.realization.toRealization := sorry

/-- The neutral realization map underlying a total composite is the composite map. -/
@[simp, stacks 015N "neutral realization map of a total composite"]
theorem comp_toMap {S T U : Total G RF RGF} (f : S ⟶ T) (g : T ⟶ U) :
    (f ≫ g).map.toMap =
      FilteredComplex.SpectralSequence.Realization.Map.comp f.map.toMap g.map.toMap := sorry

/-- Forget a total Grothendieck realization to its neutral filtered spectral-sequence realization. -/
@[stacks 015N "neutral realization functor from total Grothendieck spectral sequences"]
noncomputable def forgetRealization :
    Total G RF RGF ⥤ FilteredComplex.SpectralSequence.Realization (C := C) where
  obj S := S.realization.toRealization
  map f := f.map.toMap
  map_id := id_toMap
  map_comp := comp_toMap

/-- The object map of `forgetRealization` returns the underlying neutral realization. -/
@[simp, stacks 015N "neutral realization functor from total Grothendieck spectral sequences"]
theorem forgetRealization_obj (S : Total G RF RGF) :
    forgetRealization.obj S = S.realization.toRealization := sorry

/-- The morphism map of `forgetRealization` returns the underlying neutral realization map. -/
@[simp, stacks 015N "neutral realization functor from total Grothendieck spectral sequences"]
theorem forgetRealization_map {S T : Total G RF RGF} (f : S ⟶ T) :
    forgetRealization.map f = f.map.toMap := sorry

end Total

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence
