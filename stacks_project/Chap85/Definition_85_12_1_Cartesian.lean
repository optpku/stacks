/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_12_1_Module
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleDescent

/-!
# Cartesian sheaves, modules, and derived objects on C_total

A sheaf, module, or derived object on the total simplicial site is cartesian
when every simplex-operator comparison is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan

#check (CategoryTheory.SimplicialSites.isCartesian_iff C J :
  ∀ F : Sheaf (SimplicialSites.topology C J) (Type w),
    SimplicialSites.IsCartesian C J F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (SimplicialSites.transition C J φ F))

end CategoryTheory.SimplicialSites
