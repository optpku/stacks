/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-! Filtered-colimit generation for constructible étale sheaves. -/

/-- Every sheaf of sets on the small étale site of a quasi-compact, quasi-separated scheme is a
filtered colimit of constructible étale sheaves of sets. -/
theorem isConstructibleEtaleSet_ind
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) G) F := sorry

/-- Every sheaf of modules over a Noetherian ring on the small étale site of a quasi-compact,
quasi-separated scheme is a filtered colimit of constructible étale module sheaves. -/
theorem isConstructibleEtaleModule_ind
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    ObjectProperty.ind.{max (u + 1) w}
      (fun G ↦ IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G) F := sorry

/-- Every locally torsion abelian sheaf on the small étale site of a quasi-compact,
quasi-separated scheme is a filtered colimit of constructible étale abelian sheaves. -/
theorem isConstructibleEtaleAddCommGrp_ind
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G) F := sorry

end CategoryTheory.Sheaf
