/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Normal.Locality
import StacksCheckRecall

open scoped AlgebraicGeometry

universe u

/- Lemma 28.7.2: a scheme is normal if and only if the section ring of every
affine open is normal. -/
@[stacks 033J] #check
  (AlgebraicGeometry.Scheme.isNormal_iff_forall_affineOpen :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      X.isNormal ↔
        ∀ U : X.affineOpens, _root_.IsNormalRing (Γ(X, U)))

#check
  (AlgebraicGeometry.Scheme.isNormal_iff_exists_affineOpenCover :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      X.isNormal ↔
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, _root_.IsNormalRing (Γ(X, (𝒰.f i).opensRange)))

#check
  (AlgebraicGeometry.Scheme.isNormal_iff_exists_openCover :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      X.isNormal ↔
        ∃ 𝒰 : X.OpenCover,
          ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.isNormal)

#check
  (AlgebraicGeometry.Scheme.isNormal_toScheme :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (_ : X.isNormal) (U : X.Opens),
      U.toScheme.isNormal)
