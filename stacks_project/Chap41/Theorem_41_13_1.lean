/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.EtaleCoordinates
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

/- Theorem 41.13.1: a morphism smooth at a point admits affine source and target
neighborhoods on which it factors through an étale morphism to a relative affine space. -/
@[stacks 039Q] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_etale_affineSpaceNeighborhood :
    ∀ {X Y : Scheme} {f : X ⟶ Y} {x : X}, f.SmoothAt x →
      ∃ d : ℕ, ∃ V : Y.affineOpens, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
            ∃ π : (U : X.Opens).toScheme ⟶
                AffineSpace (Fin d) (V : Y.Opens).toScheme,
              Etale π ∧
                π ≫ (AffineSpace (Fin d) (V : Y.Opens).toScheme ↘
                  (V : Y.Opens).toScheme) = f.resLE V U e)
