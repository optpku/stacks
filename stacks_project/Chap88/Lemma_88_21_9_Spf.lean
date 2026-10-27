/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Affine formal-spectrum maps

The algebra-induced maps and their power-stage specifications are re-exported
from their mathematical owner, preserving the chapter import surface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.specOver :
  ∀ {A : Type u} [CommRing A] {S : Scheme.{u}},
    (Spec (.of A) ⟶ S) → AlgebraicSpace S)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.closedImmersion :
  ∀ {A : Type u} [CommRing A] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A),
    specOver (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hA) ⟶ specOver hA)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.algebraMapOver :
  ∀ {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S),
    specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA) ⟶ specOver hA)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfAdicCompletionMap :
  ∀ {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A),
    completionAlongSubspace
        (closedImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))) ⟶
      completionAlongSubspace (closedImmersion hA I))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.powerStageMap :
  ∀ {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S),
    powerStage (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
      (I.map (algebraMap A B)) n ⟶ powerStage hA I n)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.powerThickeningsMap :
  ∀ {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S),
    powerThickenings (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
      (I.map (algebraMap A B)) ⟶ powerThickenings hA I)

#check (AlgebraicGeometry.AlgebraicSpace.Points :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type (u + 1))
