/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.EtaleCoordinates
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 29.36.20: a morphism smooth at a point admits étale coordinates on an
affine neighborhood over any affine neighborhood of the image point.
-/
@[stacks 054L] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_etale_affineSpace :
    {X Y : Scheme} → {f : X ⟶ Y} → {x : X} → f.SmoothAt x →
      (V : Y.affineOpens) → f x ∈ (V : Y.Opens) →
        ∃ d : ℕ, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
            ∃ π : ((U : X.Opens).toScheme) ⟶
                AffineSpace (Fin d) ((V : Y.Opens).toScheme),
              Etale π ∧
                π ≫ (AffineSpace (Fin d) ((V : Y.Opens).toScheme) ↘
                  ((V : Y.Opens).toScheme)) =
                    f.resLE (V : Y.Opens) (U : X.Opens) e)
