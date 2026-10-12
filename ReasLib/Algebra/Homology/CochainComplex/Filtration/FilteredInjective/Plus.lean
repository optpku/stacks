/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Filtered-Injective Presentations

This leaf converts the bounded-below-complex presentation in the filtered-injective full
subcategory into the canonical `FilteredInjectivePlus` owner.  It removes repeated local subtype
packages from horseshoe and resolution arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Forget a bounded-below complex in the filtered-injective full subcategory to a complex of
finite filtered objects. -/
noncomputable abbrev fromSubcategory
    (I : CochainComplex.Plus (FilteredObject.Finite.FilteredInjective.category C)) :
    CochainComplex (FilteredObject.Finite.category C) ℤ :=
  (CochainComplex.Plus.ι (FilteredObject.Finite.FilteredInjective.category C) ⋙
    (FilteredObject.Finite.FilteredInjective.inclusion C).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I

/-- Each term of `fromSubcategory I` is filtered injective. -/
theorem fromSubcategory_term_mem
    (I : CochainComplex.Plus (FilteredObject.Finite.FilteredInjective.category C)) (n : ℤ) :
    FilteredObject.Finite.FilteredInjective.property C ((fromSubcategory I).X n) := sorry

/-- Package a bounded-below complex in the filtered-injective full subcategory in the canonical
termwise filtered-injective owner. The lower bound is inherited from the input `Plus` object. -/
noncomputable def ofSubcategory
    (I : CochainComplex.Plus (FilteredObject.Finite.FilteredInjective.category C)) :
    CochainComplex.FilteredInjectivePlus C :=
  ⟨⟨fromSubcategory I,
      (CochainComplex.plus_iff (FilteredObject.Finite.category C) (fromSubcategory I)).2 <| by
        obtain ⟨a, hI⟩ := I.property
        refine ⟨a, ?_⟩
        exact (isStrictlyGE_mapHomologicalComplex_obj_iff
          (K := I.obj) (FilteredObject.Finite.FilteredInjective.inclusion C) a).2 hI⟩,
    fun n ↦ fromSubcategory_term_mem I n⟩

/-- Including `ofSubcategory I` into all finite filtered complexes recovers its original
underlying complex. -/
theorem ι_obj_ofSubcategory
    (I : CochainComplex.Plus (FilteredObject.Finite.FilteredInjective.category C)) :
    (CochainComplex.FilteredInjectivePlus.ι C).obj (ofSubcategory I) = fromSubcategory I := sorry

end CochainComplex.FilteredInjectivePlus
