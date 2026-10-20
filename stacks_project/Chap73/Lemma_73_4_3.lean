/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

/- Lemma 73.4.3 (1): an isomorphism gives a singleton étale covering. -/
@[stacks 041F] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_singleton_of_isIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
      Presieve.ofArrows (fun _ : Unit ↦ X') (fun _ : Unit ↦ f) ∈
        etalePrecoverage.coverings X)

/- Lemma 73.4.3 (2): indexed composition preserves étale coverings. -/
@[stacks 041F] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_comp :
    ∀ {S : Scheme.{u}} {ι : Type v} {κ : ι → Type w}
      {X : AlgebraicSpace S} {Xᵢ : ι → AlgebraicSpace S}
      (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage.coverings X →
        ∀ {Xᵢⱼ : (i : ι) → κ i → AlgebraicSpace S}
          (g : (i : ι) → (j : κ i) → Xᵢⱼ i j ⟶ Xᵢ i),
          (∀ i, Presieve.ofArrows (Xᵢⱼ i) (g i) ∈
            etalePrecoverage.coverings (Xᵢ i)) →
            Presieve.ofArrows (fun ij : Sigma κ ↦ Xᵢⱼ ij.1 ij.2)
              (fun ij : Sigma κ ↦ g ij.1 ij.2 ≫ f ij.1) ∈
                etalePrecoverage.coverings X)

/- Lemma 73.4.3 (3): base change along any morphism of algebraic spaces preserves
étale coverings. -/
@[stacks 041F] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_pullback :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} {ι : Type v}
      {Xᵢ : ι → AlgebraicSpace S} (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage.coverings X →
        ∀ (g : X' ⟶ X),
          Presieve.ofArrows (fun i ↦ pullback g (f i))
            (fun i ↦ pullback.fst g (f i)) ∈
              etalePrecoverage.coverings X')
