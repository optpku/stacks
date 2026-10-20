/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import Mathlib.CategoryTheory.Presentable.Finite

@[expose] public section

open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- A constructible set-valued étale sheaf on a quasi-compact quasi-separated scheme is
finitely presentable. -/
theorem isFinitelyPresentable_of_isConstructibleEtaleSet
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F) :
    IsFinitelyPresentable.{u + 1} F := sorry

/-- Concrete constructibility of a set-valued étale sheaf on a quasi-compact quasi-separated
scheme supplies its finite-presentability instance. -/
instance instIsFinitelyPresentableEtaleSetOfConstructible
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [Fact (IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) ↦
        IsFiniteLocallyConstant G) F)] :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_isConstructibleEtaleSet F Fact.out

/-- A constructible abelian-group-valued étale sheaf on a quasi-compact quasi-separated
scheme is finitely presentable. -/
theorem isFinitelyPresentable_of_isConstructibleEtaleAddCommGrp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    IsFinitelyPresentable.{u + 1} F := sorry

/-- Concrete constructibility of an abelian-group-valued étale sheaf on a quasi-compact
quasi-separated scheme supplies its finite-presentability instance. -/
instance instIsFinitelyPresentableEtaleAddCommGrpOfConstructible
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Fact (IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
        IsFiniteLocallyConstantAddCommGrp G) F)] :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_isConstructibleEtaleAddCommGrp F Fact.out

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/-- A constructible étale sheaf of modules over a Noetherian ring on a quasi-compact
quasi-separated scheme is finitely presentable. -/
theorem isFinitelyPresentable_of_isConstructibleEtaleModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F) :
    IsFinitelyPresentable.{max (u + 1) w} F := sorry

/-- Concrete constructibility of an étale module sheaf over a Noetherian ring on a
quasi-compact quasi-separated scheme supplies its finite-presentability instance. -/
instance instIsFinitelyPresentableEtaleModuleOfConstructible
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))
    [Fact (IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F)] :
    IsFinitelyPresentable.{max (u + 1) w} F :=
  isFinitelyPresentable_of_isConstructibleEtaleModule F Fact.out

end CategoryTheory.Sheaf
