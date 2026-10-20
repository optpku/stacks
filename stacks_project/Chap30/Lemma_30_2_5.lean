/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.2.5: a scheme has affine absolute diagonal if and only if intersections of affine
opens are affine. -/
@[stacks 0BDX] #check
  (AlgebraicGeometry.Scheme.affineDiagonal_iff_affineOpenIntersections :
    ∀ (X : Scheme.{u}), IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) ↔
      ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

#check
  (AlgebraicGeometry.Scheme.exists_affineIntersectionOpenCover_of_affineOpenIntersections :
    ∀ (X : Scheme.{u}),
      (∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1)) →
        ∃ (I : Type u) (U : I → X.Opens), TopologicalSpace.IsOpenCover U ∧
          ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a)))

#check
  (AlgebraicGeometry.Scheme.affineDiagonal_of_exists_affineIntersectionOpenCover :
    ∀ (X : Scheme.{u}),
      (∃ (I : Type u) (U : I → X.Opens), TopologicalSpace.IsOpenCover U ∧
        ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a))) →
          IsAffineHom (prod.lift (𝟙 X) (𝟙 X)))

#check
  (AlgebraicGeometry.Scheme.affineDiagonal_of_isSeparated :
    ∀ (X : Scheme.{u}) [X.IsSeparated], IsAffineHom (prod.lift (𝟙 X) (𝟙 X)))
