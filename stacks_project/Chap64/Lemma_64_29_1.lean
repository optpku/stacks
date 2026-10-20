/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactSupportCoinvariants
public import stacks_project.Chap64.Lemma_64_29_1_Sheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Lemma 64.29.1. Degree-two compactly supported geometric étale cohomology is
canonically isomorphic to geometric coinvariants with inverse cyclotomic twist. -/
@[stacks 03VK] #check
  (AlgebraicGeometry.SchemeOverField.compactSupport_iso_geometricCoinvariantsTateTwist :
  {k : Type u} → [Field k] → {Λ : Type (u + 1)} → [Ring Λ] → [Finite Λ] →
  (X : SchemeOverField k) → [Curve X] → [Smooth X.hom] → [GeometricallyConnected X.hom] →
  [ConnectedSpace X.left] → [ConnectedSpace (geometricBaseChange X)] →
  [ConnectedSpace (Spec (CommRingCat.of k))] →
  [CompactSpace X.left] → [QuasiSeparatedSpace X.left] →
  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)] →
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] →
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] →
  (xbar : GeometricPoint (geometricBaseChange X)) →
  (Mρ : (finiteTypeDiscreteModule Λ
    (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory) →
  (P : Compactification.Of (Spec (CommRingCat.of k)) X) →
  (hΛ : IsUnit (Nat.card Λ : k)) →
  IsIsomorphic
    (cohomologyCompactSupportGaloisModule X P
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (associatedSheaf Λ (arithmeticPoint X xbar) Mρ)) 2)
    (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
        Gal(AlgebraicClosure k/k)).obj
      (tateTwist hΛ (geometricCoinvariants X xbar Mρ.obj))))
