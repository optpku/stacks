/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

/- Lemma 73.6.3 (1): an isomorphism gives a singleton syntomic covering. -/
@[stacks 041B] #check
  (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_singleton_of_isIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
      SyntomicCovering (fun _ : Unit ↦ Over.mk f))

/- Lemma 73.6.3 (2): indexed composition preserves syntomic coverings. -/
@[stacks 041B] #check
  (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_comp :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} {κ : ι → Type w}
      (family : ι → Over X)
      (refinement : (i : ι) → κ i → Over (family i).left),
      SyntomicCovering family →
        (∀ i, SyntomicCovering (refinement i)) →
          SyntomicCovering (fun p : Sigma κ ↦
            Over.mk ((refinement p.1 p.2).hom ≫ (family p.1).hom)))

/- Lemma 73.6.3 (3): base change along any morphism of algebraic spaces preserves
syntomic coverings. -/
@[stacks 041B] #check
  (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_pullback :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} {ι : Type v}
      (family : ι → Over X),
      SyntomicCovering family →
        ∀ (g : X' ⟶ X),
          SyntomicCovering (fun i ↦ Over.mk (pullback.fst g (family i).hom)))
