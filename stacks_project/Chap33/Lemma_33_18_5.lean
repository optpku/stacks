/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.TangentPresentation

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.18.5: for a locally finite type morphism, an affine neighborhood of a point has
either an immersion into relative affine space of dimension one greater than the tangent-space
rank or a closed immersion into a smooth scheme of that rank. -/
@[stacks 0CBL] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_tangentRankPresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens))
      (r : ℕ) (hr : r = Module.finrank (X.residueField x)
        (AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x)),
      (∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          ∃ j : (U : X.Opens).toScheme ⟶
              AffineSpace (ULift.{u} (Fin (r + 1))) (V : S.Opens).toScheme,
            IsImmersion j ∧
              j ≫ (AffineSpace (ULift.{u} (Fin (r + 1))) (V : S.Opens).toScheme ↘
                (V : S.Opens).toScheme) =
                f.resLE (V : S.Opens) (U : X.Opens) e) ∨
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
            ∃ D : Scheme.{u},
              ∃ g : D ⟶ (V : S.Opens).toScheme,
                SmoothOfRelativeDimension r g ∧
                  ∃ j : (U : X.Opens).toScheme ⟶ D,
                    IsClosedImmersion j ∧
                      j ≫ g = f.resLE (V : S.Opens) (U : X.Opens) e)
