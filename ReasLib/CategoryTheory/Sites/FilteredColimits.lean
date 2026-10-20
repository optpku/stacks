module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.FiniteRefinement

/-!
# Filtered colimits of sheaves on a site

This module packages the finite-overlap hypotheses on a site object and the resulting comparison
between filtered colimits of sheaf sections and sections of the colimit sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily.Over

universe z w v u

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C}

/-- A covering family has quasi-compact pairwise overlaps when every pullback of two of its
members is quasi-compact. -/
@[stacks 00YQ "quasi-compact pairwise overlaps"]
def pairwiseOverlaps (J : GrothendieckTopology C)
    {U : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} U)
    [𝒰.toPresieve.HasPairwisePullbacks] : Prop :=
  ∀ i j : 𝒰.index,
    J.QuasiCompactObject (Limits.pullback (𝒰.obj i).hom (𝒰.obj j).hom)

/-- Every covering family admits a finite refinement with quasi-compact pairwise overlaps. -/
@[stacks 00YQ "finite cofinal refinement with quasi-compact overlaps"]
class HasCofinalRefinement (J : GrothendieckTopology C) (U : C) : Prop where
  /-- Every covering family admits a finite covering refinement whose pairwise pullbacks are
  available and quasi-compact. -/
  finite_refinement
    (𝒰 : SemiRepresentableFamily.Over.{max u v} U)
    (h_cover : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱 ⟶ 𝒰) (_ : 𝒱.toPresieve.HasPairwisePullbacks),
      𝒱.toSieve ∈ J U ∧ pairwiseOverlaps J 𝒱

/-- A finite quasi-compact-overlap refinement implies the ordinary finite-refinement property. -/
instance (priority := 100) HasCofinalRefinement.toFiniteRefinement
    [HasCofinalRefinement J U] :
    HasFiniteRefinement J U := sorry

/-- A finite quasi-compact-overlap refinement implies quasi-compactness of the object. -/
theorem HasCofinalRefinement.quasiCompactObject
    (hU : HasCofinalRefinement J U) :
    J.QuasiCompactObject U := sorry

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

namespace Sites.FilteredColimitSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type w} [Category I]

/-- The canonical comparison from the colimit of sections of a sheaf diagram to the sections of
its colimit. This is `colimit.post` for the sheaf-sections functor, named here so that results
about filtered colimits of sheaves do not need to expose its implementation. -/
noncomputable abbrev comparison {A : Type z} [Category A]
    (F : I ⥤ Sheaf J A) (U : C)
    [HasColimit F]
    [HasColimit (F ⋙ (sheafSections J A).obj (op U))] :=
  colimit.post F ((sheafSections J A).obj (op U))

variable [HasWeakSheafify J (Type (max u v z))]
variable [Small.{max u v z} I]
variable [IsFiltered I]

/-- Monic transition maps make the filtered-colimit comparison from local sections injective at
every site object. -/
theorem injective_of_mono (F : I ⥤ Sheaf J (Type (max u v z))) (U : C)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    Function.Injective (comparison F U) := sorry

/-- Quasi-compactness makes the filtered-colimit comparison from local sections injective. -/
theorem injective_of_quasiCompactObject
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U) :
    Function.Injective (comparison F U) := sorry

/-- Quasi-compactness and monic transition maps make the filtered-colimit comparison from local
sections an isomorphism. -/
theorem isIso_of_quasiCompactObject_of_mono
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    IsIso (comparison F U) := sorry

/-- Cofinal refinements with finite quasi-compact overlaps make the sections comparison
bijective. -/
@[stacks 00YQ "filtered colimit comparison from finite quasi-compact refinements"]
theorem bijective_ofCofinalRefinement
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C)
    (hU : J.HasCofinalRefinement U) :
    Function.Bijective (comparison F U) := sorry

/-- The categorical `IsIso` form of the cofinal-refinement comparison theorem. -/
@[stacks 0738 "isomorphism from finite quasi-compact refinements"]
theorem isIso_ofCofinalRefinement
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C)
    (hU : J.HasCofinalRefinement U) :
    IsIso (comparison F U) := sorry

/-- Evaluation of set-valued sheaves at an object with finite quasi-compact-overlap refinements
preserves filtered colimits.  No global sheafification hypothesis is part of this preservation
statement: `PreservesFilteredColimits` is conditional on the relevant source colimit cocones. -/
instance preservesFilteredColimits
    (U : C) [J.HasCofinalRefinement U] :
    PreservesFilteredColimits
      ((sheafSections J (Type (max u v z))).obj (op U)) := sorry

end Sites.FilteredColimitSections

end CategoryTheory

end
