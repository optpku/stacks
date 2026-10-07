module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.EtaleCoordinates
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.17.1: a closed immersion between schemes smooth over `S` is, near every
point of its source, the pullback along an étale map of a standard coordinate inclusion
`𝔸ᵐ_S ⟶ 𝔸⁽ᵐ⁺ⁿ⁾_S`. -/
@[stacks 0FUE] #check
  (AlgebraicGeometry.Scheme.Hom.exists_etaleCoordinates_of_closedImmersion :
    {S : Scheme.{u}} → (X Y : Over S) → (i : Y ⟶ X) →
      [Smooth X.hom] → [Smooth Y.hom] → [IsClosedImmersion i.left] → (y : Y.left) →
        ∃ m n : ℕ, ∃ U : X.left.Opens,
          let V := i.left ⁻¹ᵁ U
          y ∈ V ∧
            ∃ π : Over.mk (U.ι ≫ X.hom) ⟶
                Over.mk (𝔸(ULift.{u} (Fin (m + n)); S) ↘ S),
              ∃ q : Over.mk (V.ι ≫ Y.hom) ⟶
                  Over.mk (𝔸(ULift.{u} (Fin m); S) ↘ S),
                Etale π.left ∧
                  IsPullback q.left (i.left.resLE U V le_rfl)
                    (AffineSpace.standardInclusion m n S) π.left)
