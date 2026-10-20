/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 29.39.4: Let `f : X ⟶ S` be a finite-type morphism of schemes with affine base,
and let `L` be an invertible module on `X`. Then ampleness and relative ampleness of `L`,
relative very ampleness of some or all sufficiently high positive tensor powers, and the
corresponding positive-dimensional relative projective-space presentations are equivalent. -/
@[stacks 01VT] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.tfae_relative_of_finiteType_affineBase :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      [AlgebraicGeometry.IsAffine S]
      [AlgebraicGeometry.Scheme.Hom.FiniteType f],
      List.TFAE [
        AlgebraicGeometry.Scheme.Modules.IsAmple L,
        AlgebraicGeometry.RelativelyAmple f L,
        ∃ d : ℕ, 1 ≤ d ∧
          AlgebraicGeometry.RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
        ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
          AlgebraicGeometry.RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
        ∃ d : ℕ, 1 ≤ d ∧
          ∃ n : ℕ, 1 ≤ n ∧
            ∃ (P : AlgebraicGeometry.ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
              ∃ e : RingedSpace.TensorPower.sheaf L d ≅
                  (AlgebraicGeometry.Scheme.Modules.pullback i).obj P.tautologicalSheaf,
                IsImmersion i ∧ i ≫ P.hom = f,
        ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
          ∃ n : ℕ, 1 ≤ n ∧
            ∃ (P : AlgebraicGeometry.ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
              ∃ e : RingedSpace.TensorPower.sheaf L d ≅
                  (AlgebraicGeometry.Scheme.Modules.pullback i).obj P.tautologicalSheaf,
                IsImmersion i ∧ i ≫ P.hom = f])
