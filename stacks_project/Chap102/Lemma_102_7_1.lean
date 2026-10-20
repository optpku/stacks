/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ClosedSubset.Approximation
import StacksCheckRecall

/-!
# Affine finite-presentation approximation of closed subsets

A closed subset of an affine base change of a quasi-compact algebraic stack
admits an affine finite-presentation approximation avoiding a chosen base point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 102.7.1: A closed subset avoiding a base point admits an affine
finite-presentation approximation on an open neighbourhood of that point. -/
@[stacks 0H29] #check
  (AlgebraicGeometry.AlgebraicStack.existsAffineOpenApproximationAvoidingImage :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsQuasiCompact X]
    {Y Z : Over S} [IsAffine Y.left] [IsAffine Z.left]
    (f : X ⟶ GroupoidsOver.slice Y) [QuasiCompact f] (g : Z ⟶ Y)
    (z : Z.left) (T : Set (Points (pullbackAlongOver f g)))
    (hT : IsClosed T)
    (hz : Points.ofSlice z ∉ Points.map (pullbackAlongOver.snd f g) '' T),
    ∃ (V : Z.left.Opens) (hVz : z ∈ (V : Set Z.left)) (_ : IsAffine V.toScheme)
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : Over.mk (V.ι ≫ Z.hom) ⟶ Z') (b : Z' ⟶ Y)
      (_ : LocallyOfFinitePresentation b.left)
      (hcomm : a ≫ b = (Over.homMk V.ι rfl) ≫ g)
      (T' : Set (Points (pullbackAlongOver f b))) (_ : IsClosed T'),
      Points.ofSlice (a.left ⟨z, hVz⟩) ∉
          Points.map (pullbackAlongOver.snd f b) '' T' ∧
        Points.map (pullbackAlongOver.map f
          ((Over.homMk V.ι rfl : Over.mk (V.ι ≫ Z.hom) ⟶ Z) ≫ g) b a hcomm) ''
          (Points.map (pullbackAlongOver.map f
            ((Over.homMk V.ι rfl : Over.mk (V.ι ≫ Z.hom) ⟶ Z) ≫ g) g
            (Over.homMk V.ι rfl) rfl) ⁻¹' T) ⊆ T')
