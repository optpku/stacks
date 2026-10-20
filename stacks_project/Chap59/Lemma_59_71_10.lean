/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ScalarExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace CategoryTheory.Sheaf

/- Lemma 59.71.10: for a homomorphism `f : Λ →+* Λ'` of Noetherian rings and a scheme `X`,
the scalar extension `F ⊗_{Λ̲} Λ̲'` of a constructible sheaf of `Λ`-modules on
`Xₑₜ` is a constructible sheaf of `Λ'`-modules. -/
@[stacks 0GKB] #check
  (CategoryTheory.Sheaf.IsConstructibleEtaleModule.scalarExtension :
    {X : Scheme.{u}} → {Λ Λ' : Type v} → [CommRing Λ] → [CommRing Λ'] →
      [IsNoetherianRing Λ] → [IsNoetherianRing Λ'] →
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)] →
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ')] →
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)] →
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ')] →
      [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] →
      [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ'),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] →
      (f : Λ →+* Λ') →
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) →
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{v} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) F →
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{v} Λ')
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ')) ↦
          IsFiniteTypeLocallyConstantModule G)
        (CategoryTheory.Sheaf.scalarExtensionSheaf f F))

end CategoryTheory.Sheaf
