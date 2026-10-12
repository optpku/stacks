/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks as filtered colimits

This file gives the filtered-colimit construction of a presheaf stalk and its comparison with
the ordinary stalk after applying a functor that preserves filtered colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopCat
open TopologicalSpace

universe v w z

noncomputable section

namespace TopCat.Presheaf

variable {C : Type v} [Category.{w} C] [HasFilteredColimits C]
variable {X : TopCat.{w}} (x : X)

/-- The stalk functor formed using only filtered colimits, as the colimit of the restriction of a
presheaf to open neighborhoods of a point. -/
noncomputable abbrev filteredStalkFunctor : X.Presheaf C ⥤ C :=
  (whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op ⋙ colim

/-- The stalk of a `C`-valued presheaf formed using only filtered colimits. -/
noncomputable abbrev filteredStalk (ℱ : X.Presheaf C) : C :=
  (filteredStalkFunctor x).obj ℱ

section General

variable {D : Type z} [Category.{w} D] [HasFilteredColimits D]
variable (F : C ⥤ D) [PreservesFilteredColimits F]

/-- A filtered-colimit-preserving functor commutes with the filtered stalk functor. -/
noncomputable def filteredStalkCompIsoOf :
    filteredStalkFunctor (C := C) x ⋙ F ≅
      (whiskeringRight (Opens X)ᵒᵖ C D).obj F ⋙
        filteredStalkFunctor (C := D) x :=
  isoWhiskerLeft
    ((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op)
    (preservesColimitNatIso F)

/-- Objectwise compatibility of filtered stalks with a filtered-colimit-preserving functor. -/
noncomputable abbrev stalkCompIsoOf (ℱ : X.Presheaf C) :
    F.obj (filteredStalk x ℱ) ≅ filteredStalk x (ℱ ⋙ F) :=
  (filteredStalkCompIsoOf x F).app ℱ

end General

variable (F : C ⥤ Type w) [PreservesFilteredColimits F]

/-- Applying a filtered-colimit-preserving functor after the filtered stalk functor is naturally
isomorphic to taking the ordinary set-valued stalk after postcomposition. -/
noncomputable def filteredStalkCompIso :
    filteredStalkFunctor x ⋙ F ≅
      (whiskeringRight (Opens X)ᵒᵖ C (Type w)).obj F ⋙ stalkFunctor (Type w) x :=
  isoWhiskerLeft
    ((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op)
    (preservesColimitNatIso F)

/-- The objectwise comparison between the image of a filtered stalk and the stalk of the
postcomposed set-valued presheaf. -/
noncomputable abbrev stalkCompIso (ℱ : X.Presheaf C) :
    F.obj (filteredStalk x ℱ) ≅ stalk (ℱ ⋙ F) x :=
  (filteredStalkCompIso x F).app ℱ

end TopCat.Presheaf
