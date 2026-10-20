/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.TargetLocus
import StacksCheckRecall

/-! # Largest open of the target for a local morphism property -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

/- Lemma 74.10.3: the largest good target open. -/
@[stacks 06R2] #check (AlgebraicGeometry.AlgebraicSpace.targetLocus_isLargest :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    P (pullback.snd f (targetLocus P f).ι) ∧
      ∀ V : OpenSubspace Y, P (pullback.snd f V.ι) →
        ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι)

/- Lemma 74.10.3: factorization through the target locus. -/
@[stacks 06R2] #check (AlgebraicGeometry.AlgebraicSpace.factorsThrough_targetLocus :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g)
    (hf : P (pullback.snd f g)),
    ∃ χ : Y' ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = g)

/- Lemma 74.10.3: compatibility with admissible base change. -/
@[stacks 06R2] #check (AlgebraicGeometry.AlgebraicSpace.targetLocus_inverseImage :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g),
    (targetLocus P (pullback.snd f g)).pointsSet =
      Points.map g ⁻¹' (targetLocus P f).pointsSet)

/- Lemma 74.10.3: compatibility with every covering member. -/
@[stacks 06R2] #check (AlgebraicGeometry.AlgebraicSpace.targetLocus_inverseImage_cover :
    ∀ {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : Precoverage.ZeroHypercover.{v} K Y) (i : 𝒰.I₀),
    (targetLocus P (pullback.snd f (𝒰.f i))).pointsSet =
      Points.map (𝒰.f i) ⁻¹' (targetLocus P f).pointsSet)

