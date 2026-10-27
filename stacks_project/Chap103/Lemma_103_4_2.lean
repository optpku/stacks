/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FlatCover
import StacksCheckRecall

/-!
# Detection of monomorphisms, epimorphisms, and isomorphisms in QCoh

On an algebraic stack, a morphism of quasi-coherent modules is a monomorphism,
epimorphism, or isomorphism if and only if each small-étale restriction along
a jointly surjective family of flat objects is so.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

/- Lemma 103.4.2 (1): monomorphisms are detected by small-étale restrictions
along a jointly surjective family of flat objects. -/
@[stacks 0GQF] #check
  (AlgebraicGeometry.AlgebraicStack.mono_iff_forall_restrict :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {I : Type v} {U : I → Over S} {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X}
      [∀ i, Flat (x i)] (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G),
      Mono φ ↔ ∀ i, Mono ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ))

/- Lemma 103.4.2 (2): epimorphisms are detected by small-étale restrictions
along a jointly surjective family of flat objects. -/
@[stacks 0GQF] #check
  (AlgebraicGeometry.AlgebraicStack.epi_iff_forall_restrict :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {I : Type v} {U : I → Over S} {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X}
      [∀ i, Flat (x i)] (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G),
      Epi φ ↔ ∀ i, Epi ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ))

/- Lemma 103.4.2 (3): isomorphisms are detected by small-étale restrictions
along a jointly surjective family of flat objects. -/
@[stacks 0GQF] #check
  (AlgebraicGeometry.AlgebraicStack.isIso_iff_forall_restrict :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {I : Type v} {U : I → Over S} {x : ∀ i, GroupoidsOver.slice (U i) ⟶ X}
      [∀ i, Flat (x i)] (h_surj : jointlySurjective x) {F G : QCoh X} (φ : F ⟶ G),
      IsIso φ ↔ ∀ i, IsIso ((QCoh.restrictToSmallEtale X (evalId (x i))).map φ))

