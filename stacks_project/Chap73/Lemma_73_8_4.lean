/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph.Stability
import StacksCheckRecall

/-!
# Stability of ph covering families of algebraic spaces

Ph covering families of algebraic spaces are stable under singleton
isomorphisms, dependent composition, and slice base change along an arbitrary
morphism.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.8.4 (1): a singleton isomorphism is a ph covering. -/
@[stacks 0DFJ] #check
  (AlgebraicGeometry.AlgebraicSpace.phCovering_singleton_of_isIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
      PhCovering (fun _ : Unit ↦ X') (fun _ ↦ f))

/- Lemma 73.8.4 (2): dependent composites of ph coverings are ph coverings. -/
@[stacks 0DFJ] #check
  (AlgebraicGeometry.AlgebraicSpace.phCovering_comp :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {ι : Type v} {κ : ι → Type w} {Xi : ι → AlgebraicSpace S}
      (f : ∀ i, Xi i ⟶ X) {Xij : (i : ι) → κ i → AlgebraicSpace S}
      (g : (i : ι) → (j : κ i) → Xij i j ⟶ Xi i)
      [PhCovering Xi f] [∀ i, PhCovering (Xij i) (g i)],
      PhCovering (fun p : Sigma κ ↦ Xij p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1))

/- Lemma 73.8.4 (3): ph coverings are stable under arbitrary base change. -/
@[stacks 0DFJ] #check
  (AlgebraicGeometry.AlgebraicSpace.phCovering_pullback :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
      {ι : Type v} {Xi : ι → AlgebraicSpace S} (f : ∀ i, Xi i ⟶ X)
      [PhCovering Xi f] (g : X' ⟶ X),
      PhCovering (fun i ↦ overPullbackObj g (Over.mk (f i)))
        (fun i ↦ overPullbackSnd g (Over.mk (f i))))

end AlgebraicGeometry.AlgebraicSpace
