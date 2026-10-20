/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.CompleteDVR

/-!
# Complete discrete valuation ring formal spectra

The formal spectrum consists of morphisms that fppf-locally factor through a
maximal-ideal power stage. Extensions of complete discrete valuation rings
induce the canonical contravariant morphisms of these formal spectra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace IsLocalRing

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.spf :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S),
    (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.FormalAlgebraicSpace.dvrStageι :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S),
    yoneda.obj (powerStage structureHom (maximalIdeal R) n) ⟶ spf R structureHom)

#check (AlgebraicGeometry.FormalAlgebraicSpace.spfPresheafToSpf :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S),
    spfAdicCompletion structureHom (maximalIdeal R) ⟶ spf R structureHom)

#check (AlgebraicGeometry.FormalAlgebraicSpace.spfMap :
  ∀ (R R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [IsCompleteLocalRing R'] [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S),
    spf R' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      spf R structureHom)
