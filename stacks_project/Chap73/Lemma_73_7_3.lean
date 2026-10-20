/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

/- Lemma 73.7.3 (1): an isomorphism gives a singleton fppf covering. -/
@[stacks 03Y9] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_singleton_of_isIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
      Presieve.singleton f ∈ (fppfPrecoverage S).coverings X)

/- Lemma 73.7.3 (2): indexed composition preserves fppf coverings. -/
@[stacks 03Y9] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_comp :
    ∀ {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
      {Xᵢ : ι → AlgebraicSpace S} (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ (fppfPrecoverage S).coverings X →
        ∀ {J : ι → Type w} {Xᵢⱼ : (i : ι) → J i → AlgebraicSpace S}
          (g : (i : ι) → (j : J i) → Xᵢⱼ i j ⟶ Xᵢ i),
          (∀ i, Presieve.ofArrows (Xᵢⱼ i) (g i) ∈
            (fppfPrecoverage S).coverings (Xᵢ i)) →
            Presieve.ofArrows (fun ij : Sigma J ↦ Xᵢⱼ ij.1 ij.2)
              (fun ij ↦ g ij.1 ij.2 ≫ f ij.1) ∈
                (fppfPrecoverage S).coverings X)

/- Lemma 73.7.3 (3): pullback preserves fppf coverings. -/
@[stacks 03Y9] #check
  (AlgebraicGeometry.AlgebraicSpace.fppfCovering_pullback :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} {ι : Type v}
      {Xᵢ : ι → AlgebraicSpace S} (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ (fppfPrecoverage S).coverings X →
        ∀ (g : X' ⟶ X),
          Presieve.ofArrows (fun i ↦ pullback g (f i))
            (fun i ↦ pullback.fst g (f i)) ∈
              (fppfPrecoverage S).coverings X')
