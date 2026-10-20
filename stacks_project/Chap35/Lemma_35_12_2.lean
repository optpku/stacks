/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 35.12.2 (1): a module presheaf parasitic for a standard topology has
zero cohomology in every degree over each scheme whose structure morphism has
the corresponding standard geometric property. -/
@[stacks 0755] #check
  (PresheafOfModules.IsParasitic.isZero_cohomology :
    ∀ {S : Scheme.{u}}
      {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
      {τ : StandardTopology} (hℱ : PresheafOfModules.IsParasitic ℱ τ)
      (U : Over S) (hU : τ.precoverage.morphismProperty U.hom) (p : ℕ)
      [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsZero (PresheafOfModules.standardCohomology ℱ τ U p))

/- Lemma 35.12.2 (2): a parasitic module presheaf has zero cohomology in every
degree, for every standard topology, over each scheme flat over the base. -/
@[stacks 0755] #check
  (PresheafOfModules.IsParasiticOne.isZero_cohomology :
    ∀ {S : Scheme.{u}}
      {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
      (hℱ : PresheafOfModules.IsParasiticOne ℱ)
      (U : Over S) (hU : Flat U.hom) (τ : StandardTopology) (p : ℕ)
      [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsZero (PresheafOfModules.standardCohomology ℱ τ U p))
