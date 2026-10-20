/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism.ZeroDimensional
import StacksCheckRecall

/-!
# Monomorphisms into disjoint unions of zero-dimensional local spectra

A monomorphism of algebraic spaces into a disjoint union of spectra of
zero-dimensional local rings over a scheme is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.19.1: Let `S` be a scheme. Let `Y` be a disjoint union of spectra of
zero-dimensional local rings over `S`. Let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `S`. Then `f` is representable, i.e., `X` is a scheme. -/
@[stacks 06RZ] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_mono_to_zeroDimensionalLocalCoproduct :
    ∀ {S : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Ring.KrullDimLE 0 (A i)] (σ : ∀ i, Spec (.of (A i)) ⟶ S)
    {X Y : AlgebraicSpace S} (e : Y ≅ ofOver (Over.mk (Sigma.desc σ)))
    (f : X ⟶ Y) [Mono f], yoneda.relativelyRepresentable f)
