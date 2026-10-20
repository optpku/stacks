/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard.MorphismProperty
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal

/-!
# Cohomology of parasitic module presheaves

This module provides the functorial cohomology of the additive sheafification
of a module presheaf on a standard big site and its parasitic vanishing API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace PresheafOfModules

/-- The functor sending a module presheaf on schemes over `S` to the degree-`p`
cohomology of its associated additive sheaf over `U` for the standard topology
`τ`. -/
noncomputable def standardCohomologyFunctor
    (S : Scheme.{u}) (τ : StandardTopology) (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) ⥤
      AddCommGrpCat.{u} :=
  PresheafOfModules.toPresheaf (ringPresheaf S.overStructurePresheaf) ⋙
    presheafToSheaf (τ.overTopology S) AddCommGrpCat.{u} ⋙
      Sheaf.cohomologyPresheafFunctor (τ.overTopology S) p ⋙
        (CategoryTheory.evaluation (Over S)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The degree-`p` cohomology over `U` of the additive sheaf associated to a
module presheaf on the standard `τ`-site over `S`. -/
abbrev standardCohomology
    {S : Scheme.{u}}
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf))
    (τ : StandardTopology) (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  (standardCohomologyFunctor S τ U p).obj ℱ

namespace IsParasitic

/-- A module presheaf parasitic for a standard topology has zero cohomology
in every degree over a scheme whose structure morphism belongs to the
topology's precoverage morphism property. -/
theorem isZero_cohomology
    {S : Scheme.{u}}
    {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    {τ : StandardTopology} (hℱ : IsParasitic ℱ τ)
    (U : Over S) (hU : τ.precoverage.morphismProperty U.hom) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsZero (standardCohomology ℱ τ U p) := sorry

end IsParasitic

namespace IsParasiticOne

/-- A parasitic-one module presheaf has zero cohomology in every degree and
for every standard topology over a scheme flat over the base. -/
theorem isZero_cohomology
    {S : Scheme.{u}}
    {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    (hℱ : IsParasiticOne ℱ) (U : Over S) (hU : Flat U.hom)
    (τ : StandardTopology) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsZero (standardCohomology ℱ τ U p) := sorry

end IsParasiticOne

end PresheafOfModules
