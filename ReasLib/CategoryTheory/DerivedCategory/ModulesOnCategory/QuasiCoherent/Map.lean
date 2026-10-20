/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of comparison-defined objects

A functor preserves a comparison-isomorphism locus as soon as target comparison maps are
invertible whenever the corresponding source comparison maps are. The resulting functor on full
subcategories is then supplied by `ObjectProperty.FullSubcategory.restrict`.
-/

@[expose] public section

open CategoryTheory

universe uC vC uC' vC' uD vD uD' vD' uE vE uE' vE'

namespace CategoryTheory.ModulesOnCategory.QuasiCoherent

variable {C : Type uC} [Category.{vC} C]
variable {C' : Type uC'} [Category.{vC'} C']
variable {D : Type uD} [Category.{vD} D]
variable {D' : Type uD'} [Category.{vD'} D']
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable {E' : C' → Type uE'} [∀ U', Category.{vE'} (E' U')]
variable {RΓ : ∀ U : C, D ⥤ E U}
variable {RΓ' : ∀ U' : C', D' ⥤ E' U'}
variable {restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U}
variable {restrict' : ∀ {U' V' : C'}, (U' ⟶ V') → E' V' ⥤ E' U'}
variable
  {comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U}
variable
  {comparison' : ∀ {U' V' : C'} (f' : U' ⟶ V'),
    RΓ' V' ⋙ restrict' f' ⟶ RΓ' U'}

/-- An object in the source comparison locus maps into the target locus when target comparison
isomorphisms follow from the corresponding source comparison isomorphisms. -/
@[stacks 0GZC "objectwise preservation of comparison-defined quasi-coherence"]
theorem map_mem (u : C' ⥤ C) (F : D ⥤ D')
    (hF : ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
      IsIso ((comparison (u.map f')).app K) →
        IsIso ((comparison' f').app (F.obj K)))
    {K : D} (hK : property RΓ restrict comparison K) :
    property RΓ' restrict' comparison' (F.obj K) := sorry

/-- A functor whose target comparison maps are controlled by source comparison maps carries the
source comparison-isomorphism locus into the target locus. -/
@[stacks 0GZC]
theorem le_inverseImage (u : C' ⥤ C) (F : D ⥤ D')
    (hF : ∀ {U' V' : C'} (f' : U' ⟶ V') {K : D},
      IsIso ((comparison (u.map f')).app K) →
        IsIso ((comparison' f').app (F.obj K))) :
    property RΓ restrict comparison ≤
      (property RΓ' restrict' comparison').inverseImage F := sorry

end CategoryTheory.ModulesOnCategory.QuasiCoherent
