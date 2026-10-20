/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening.Morphism

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.AdicThickening

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A) (G : X ⟶ Y)
    (n : ℕ+), stage X I n ⟶ stage Y I n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap_ι :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (n : ℕ+),
    stageMap I G n ≫ ι Y I n = ι X I n ≫ G)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap_toSpec :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (n : ℕ+),
    stageMap I G n ≫ toSpec Y I n = toSpec X I n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap_transition :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A) (G : X ⟶ Y) (n : ℕ+),
    stageMap I G n ≫ transition Y I n = transition X I n ≫ stageMap I G (n + 1))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap_id :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A) (n : ℕ+),
    stageMap I (𝟙 X) n = 𝟙 (stage X I n))

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.stageMap_comp :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y Z : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) (H : Y ⟶ Z) (n : ℕ+),
    stageMap I (G ≫ H) n = stageMap I G n ≫ stageMap I H n)

#check (AlgebraicGeometry.AlgebraicSpace.AdicThickening.eq_stageMap_iff :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {Y : AlgebraicSpace (Spec (CommRingCat.of A))} (I : Ideal A)
    (G : X ⟶ Y) {n : ℕ+} (g : stage X I n ⟶ stage Y I n),
    g = stageMap I G n ↔
      g ≫ ι Y I n = ι X I n ≫ G ∧ g ≫ toSpec Y I n = toSpec X I n)
