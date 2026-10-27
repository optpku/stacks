/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Associated module presentations

Compatibility checks for associated modules and their commutative and
universe-lifted presentations.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.GroupoidsOver.associatedModules :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology), Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.associatedModules_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    associatedModules X τ = SheafOfModules.{u} (associatedStructureSheaf X τ))

#check (AlgebraicGeometry.GroupoidsOver.commAssociatedModules :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology), Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.moduleTensorAssociated :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ), commAssociatedModules X τ)

#check (AlgebraicGeometry.GroupoidsOver.commAssociatedModulesLiftFunctor :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    commAssociatedModules X τ ⥤ commAssociatedModulesLift X τ)
