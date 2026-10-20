/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Closure
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

section SetValued

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- A constructible sheaf of sets on the small étale site of a Noetherian scheme is a
Noetherian object. -/
theorem IsConstructibleEtaleSet.isNoetherianObject
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F) :
    IsNoetherianObject F := sorry

/-- Every ascending chain of subobjects of a constructible étale sheaf of sets on a
Noetherian scheme is eventually constant. -/
theorem IsConstructibleEtaleSet.stabilizes_subobject_chain
    {F : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end SetValued

section AbelianGroups

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A constructible sheaf of abelian groups on the small étale site of a Noetherian scheme
is a Noetherian object. -/
theorem IsConstructibleEtaleAddCommGrp.isNoetherianObject
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    IsNoetherianObject F := sorry

/-- Every ascending chain of subobjects of a constructible étale sheaf of abelian groups on a
Noetherian scheme is eventually constant. -/
theorem IsConstructibleEtaleAddCommGrp.stabilizes_subobject_chain
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end AbelianGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/-- A constructible sheaf of modules over a Noetherian ring on the small étale site of a
Noetherian scheme is a Noetherian object. -/
theorem IsConstructibleEtaleModule.isNoetherianObject
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F) :
    IsNoetherianObject F := sorry

/-- Every ascending chain of subobjects of a constructible étale sheaf of modules over a
Noetherian ring on a Noetherian scheme is eventually constant. -/
theorem IsConstructibleEtaleModule.stabilizes_subobject_chain
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F)
    (f : ℕ →o Subobject F) :
    ∃ n, ∀ m, n ≤ m → f n = f m := sorry

end Modules

end CategoryTheory.Sheaf
