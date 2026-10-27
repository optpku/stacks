/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment

/-!
# Displayed Realizations with Functorial Abutments

This leaf organizes realizations with a functorial abutment as a displayed category.  Its total
category is the canonical ordinary category of a base object together with such a realization.
The degreewise abutment comparisons then assemble into natural isomorphisms on that total category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization.WithAbutment

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type u'} [Category.{v'} I]
variable (H : ℤ → (I ⥤ C))

namespace Displayed

private theorem realizationMap_ext {S T : Realization (C := C)}
    {m n : Realization.Map S T}
    (h_filtered : m.filteredMap = n.filteredMap)
    (h_sequence : m.sequenceMap = n.sequenceMap) : m = n := by
  cases m
  cases n
  cases h_filtered
  cases h_sequence
  rfl

private theorem map_ext {X Y : I} {f : X ⟶ Y}
    {S : WithAbutment H X} {T : WithAbutment H Y} {m n : Map H f S T}
    (h : m.toRealizationMap = n.toRealizationMap) : m = n := by
  cases m
  cases n
  cases h
  rfl

private theorem cast_toRealizationMap {X Y : I} {f g : X ⟶ Y}
    {S : WithAbutment H X} {T : WithAbutment H Y}
    (h : f = g) (m : Map H f S T) :
    (h ▸ m).toRealizationMap = m.toRealizationMap := by
  cases h
  rfl

/-- The displayed identity is a left identity after transport along the base-category identity
law. -/
theorem id_comp {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X}
    {T : WithAbutment H Y} (m : Map H f S T) :
    (Category.id_comp f) ▸ Map.comp H (Map.id H S) m = m := by
  apply map_ext H
  rw [cast_toRealizationMap H]
  apply realizationMap_ext
  · exact Category.id_comp m.filteredMap
  · exact Category.id_comp m.sequenceMap

/-- The displayed identity is a right identity after transport along the base-category identity
law. -/
theorem comp_id {X Y : I} {f : X ⟶ Y} {S : WithAbutment H X}
    {T : WithAbutment H Y} (m : Map H f S T) :
    (Category.comp_id f) ▸ Map.comp H m (Map.id H T) = m := by
  apply map_ext H
  rw [cast_toRealizationMap H]
  apply realizationMap_ext
  · exact Category.comp_id m.filteredMap
  · exact Category.comp_id m.sequenceMap

/-- Displayed composition is associative after transport along base-category associativity. -/
theorem assoc {W X Y Z : I} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {R : WithAbutment H W} {S : WithAbutment H X}
    {T : WithAbutment H Y} {U : WithAbutment H Z}
    (m : Map H f R S) (n : Map H g S T) (k : Map H h T U) :
    (Category.assoc f g h) ▸ Map.comp H (Map.comp H m n) k =
      Map.comp H m (Map.comp H n k) := by
  apply map_ext H
  rw [cast_toRealizationMap H]
  apply realizationMap_ext
  · exact Category.assoc m.filteredMap n.filteredMap k.filteredMap
  · exact Category.assoc m.sequenceMap n.sequenceMap k.sequenceMap

end Displayed

/-- Realizations with functorial abutment, displayed over their parameter objects. -/
@[stacks 012C "displayed realizations with functorial abutment"]
def displayedCategory : DisplayedCategory I where
  obj X := WithAbutment H X
  Hom f S T := Map H f S T
  id S := Map.id H S
  comp m n := Map.comp H m n
  id_comp := Displayed.id_comp H
  comp_id := Displayed.comp_id H
  assoc := Displayed.assoc H

/-- The displayed objects over `X` are precisely realizations with abutment parameter `X`. -/
@[simp, stacks 012C "displayed realizations with functorial abutment"]
theorem displayedCategory_obj (X : I) :
    (displayedCategory H).obj X = WithAbutment H X := rfl

/-- The displayed morphisms over `f` are precisely realization maps over `f`. -/
@[simp, stacks 012O "displayed maps of realizations with functorial abutment"]
theorem displayedCategory_hom {X Y : I} (f : X ⟶ Y)
    (S : WithAbutment H X) (T : WithAbutment H Y) :
    (displayedCategory H).Hom f S T = Map H f S T := rfl

/-- The total category of the displayed realization category.  This is an abbreviation for the
generic displayed-category total owner, not a second data structure. -/
abbrev Total := DisplayedCategory.Total (displayedCategory H)

/-- Forget a total realization with abutment to its base parameter. -/
abbrev forgetBase : Total H ⥤ I :=
  DisplayedCategory.Total.forget (displayedCategory H)

/-- The base parameter of a total realization is unchanged by `forgetBase`. -/
@[simp, stacks 012C "base parameter of a realization with functorial abutment"]
theorem forgetBase_obj (X : Total H) :
    (forgetBase H).obj X = X.base := rfl

/-- The base morphism of a total realization map is unchanged by `forgetBase`. -/
@[simp, stacks 012O "base morphism of a realization map with functorial abutment"]
theorem forgetBase_map {X Y : Total H} (f : X ⟶ Y) :
    (forgetBase H).map f = f.base := rfl

namespace ForgetRealization

/-- Forgetting the total identity gives the identity generic realization map. -/
theorem map_id (X : Total H) :
    ((𝟙 X : X ⟶ X).displayed).toRealizationMap =
      Realization.Map.id X.obj.toRealization := rfl

/-- Forgetting a composite total morphism gives the composite generic realization map. -/
theorem map_comp {X Y Z : Total H} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).displayed).toRealizationMap =
      Realization.Map.comp f.displayed.toRealizationMap
        g.displayed.toRealizationMap := rfl

end ForgetRealization

/-- Forget the parameter and abutment comparison, retaining the generic filtered realization. -/
@[stacks 012C "forgetful functor from realizations with functorial abutment"]
def forgetRealization : Total H ⥤ Realization (C := C) where
  obj X := X.obj.toRealization
  map f := f.displayed.toRealizationMap
  map_id := ForgetRealization.map_id H
  map_comp := ForgetRealization.map_comp H

/-- The realization underlying a total object is its stored displayed realization with the
abutment comparison forgotten. -/
@[simp, stacks 012C "forgetful functor from realizations with functorial abutment"]
theorem forgetRealization_obj (X : Total H) :
    (forgetRealization H).obj X = X.obj.toRealization := rfl

/-- The generic realization map underlying a total morphism is its stored displayed map with the
abutment square forgotten. -/
@[simp, stacks 012O "forgetful functor from realizations with functorial abutment"]
theorem forgetRealization_map {X Y : Total H} (f : X ⟶ Y) :
    (forgetRealization H).map f = f.displayed.toRealizationMap := rfl

namespace Source

/-- Degreewise homology of the underlying filtered complex maps identities to identities. -/
theorem map_id (n : ℤ) (X : Total H) :
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap ((𝟙 X : X ⟶ X).displayed).filteredMap) n =
      𝟙 (X.obj.filtered.underlying.homology n) := by
  change HomologicalComplex.homologyMap (𝟙 X.obj.filtered.underlying) n = _
  exact HomologicalComplex.homologyMap_id _ n

/-- Degreewise homology of the underlying filtered complex maps composition to composition. -/
theorem map_comp (n : ℤ) {X Y Z : Total H} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap ((f ≫ g).displayed).filteredMap) n =
      HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap f.displayed.filteredMap) n ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap g.displayed.filteredMap) n := by
  change HomologicalComplex.homologyMap
    (FilteredComplex.underlyingMap f.displayed.filteredMap ≫
      FilteredComplex.underlyingMap g.displayed.filteredMap) n = _
  exact HomologicalComplex.homologyMap_comp _ _ n

end Source

/-- Degree-`n` homology of the underlying filtered complex, functorial on the total category. -/
@[stacks 012C "source of a functorial spectral-sequence abutment"]
def source (n : ℤ) : Total H ⥤ C where
  obj X := X.obj.filtered.underlying.homology n
  map f := HomologicalComplex.homologyMap
    (FilteredComplex.underlyingMap f.displayed.filteredMap) n
  map_id := Source.map_id H n
  map_comp := Source.map_comp H n

/-- Object computation for the degreewise abutment source functor. -/
@[simp, stacks 012C "source of a functorial spectral-sequence abutment"]
theorem source_obj (n : ℤ) (X : Total H) :
    (source H n).obj X = X.obj.filtered.underlying.homology n := rfl

/-- Morphism computation for the degreewise abutment source functor. -/
@[simp, stacks 012O "source of a functorial spectral-sequence abutment"]
theorem source_map (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (source H n).map f = HomologicalComplex.homologyMap
      (FilteredComplex.underlyingMap f.displayed.filteredMap) n := rfl

/-- The degree-`n` functorial abutment target on the total realization category. -/
@[stacks 012C "target of a functorial spectral-sequence abutment"]
abbrev target (n : ℤ) : Total H ⥤ C :=
  forgetBase H ⋙ H n

/-- Object computation for the degreewise functorial abutment target. -/
@[simp, stacks 012C "target of a functorial spectral-sequence abutment"]
theorem target_obj (n : ℤ) (X : Total H) :
    (target H n).obj X = (H n).obj X.base := rfl

/-- Morphism computation for the degreewise functorial abutment target. -/
@[simp, stacks 012O "target of a functorial spectral-sequence abutment"]
theorem target_map (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (target H n).map f = (H n).map f.base := rfl

/-- The selected degreewise abutment comparisons form a natural isomorphism on the total
category of realizations. -/
@[stacks 012C "natural isomorphism of a functorial spectral-sequence abutment"]
noncomputable def abutmentComparison (n : ℤ) :
    source H n ≅ target H n :=
  NatIso.ofComponents (fun X => X.obj.abutmentIso n)
    (fun f => Map.abutment_hom H f.displayed n)

/-- A component of the natural abutment comparison is the comparison stored by the displayed
realization. -/
@[simp, stacks 012C "natural isomorphism of a functorial spectral-sequence abutment"]
theorem abutmentComparison_app (n : ℤ) (X : Total H) :
    (abutmentComparison H n).app X = X.obj.abutmentIso n := by
  apply Iso.ext
  rfl

/-- The forward component of the natural abutment comparison is the stored comparison. -/
@[simp, stacks 012C "natural isomorphism of a functorial spectral-sequence abutment"]
theorem abutmentComparison_hom_app (n : ℤ) (X : Total H) :
    (abutmentComparison H n).hom.app X = (X.obj.abutmentIso n).hom := rfl

/-- The inverse component of the natural abutment comparison is the inverse stored comparison. -/
@[simp, stacks 012C "natural isomorphism of a functorial spectral-sequence abutment"]
theorem abutmentComparison_inv_app (n : ℤ) (X : Total H) :
    (abutmentComparison H n).inv.app X = (X.obj.abutmentIso n).inv := rfl

/-- Naturality of the forward degreewise abutment comparison in a total realization map. -/
@[reassoc, stacks 012O "naturality of a functorial spectral-sequence abutment"]
theorem abutmentComparison_hom_naturality
    (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (source H n).map f ≫ (abutmentComparison H n).hom.app Y =
      (abutmentComparison H n).hom.app X ≫ (target H n).map f := by
  exact (f.displayed.abutmentSq n).w

/-- Naturality of the inverse degreewise abutment comparison in a total realization map. -/
@[reassoc, stacks 012O "inverse naturality of a functorial spectral-sequence abutment"]
theorem abutmentComparison_inv_naturality
    (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (target H n).map f ≫ (abutmentComparison H n).inv.app Y =
      (abutmentComparison H n).inv.app X ≫ (source H n).map f := by
  exact (f.displayed.abutmentSq n).vert_inv.w

/-- Conjugating a target abutment map by the comparison recovers the source map. -/
@[reassoc, stacks 012O "source-map computation for a functorial spectral-sequence abutment"]
theorem abutmentComparison_source_map
    (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (abutmentComparison H n).hom.app X ≫ (target H n).map f ≫
        (abutmentComparison H n).inv.app Y =
      (source H n).map f := by
  change (X.obj.abutmentIso n).hom ≫ (H n).map f.base ≫
    (Y.obj.abutmentIso n).inv = _
  rw [← Category.assoc, ← (f.displayed.abutmentSq n).w,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- Conjugating a source abutment map by the inverse comparison recovers the target map. -/
@[reassoc, stacks 012O "target-map computation for a functorial spectral-sequence abutment"]
theorem abutmentComparison_target_map
    (n : ℤ) {X Y : Total H} (f : X ⟶ Y) :
    (abutmentComparison H n).inv.app X ≫ (source H n).map f ≫
        (abutmentComparison H n).hom.app Y =
      (target H n).map f := by
  change (X.obj.abutmentIso n).inv ≫
    HomologicalComplex.homologyMap
      (FilteredComplex.underlyingMap f.displayed.filteredMap) n ≫
    (Y.obj.abutmentIso n).hom = _
  rw [(f.displayed.abutmentSq n).w, Iso.inv_hom_id_assoc]
  rfl

end CategoryTheory.FilteredComplex.SpectralSequence.Realization.WithAbutment
