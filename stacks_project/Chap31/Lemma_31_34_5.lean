module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Separation
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 31.34.5: if `X` is quasi-compact and quasi-separated and `U, V ⊆ X` are disjoint
quasi-compact open subschemes, then an admissible blowup separates their inverse images into a
disjoint two-open cover of its source. -/
@[stacks 080P] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      (U V : X.Opens) (hU : AlgebraicGeometry.QuasiCompact U.ι)
      (hV : AlgebraicGeometry.QuasiCompact V.ι)
      (hUV : Disjoint (U : Set X) (V : Set X)),
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
        AlgebraicGeometry.IsAdmissibleBlowup (U ⊔ V) b ∧
          ∃ X₁ X₂ : X'.Opens,
            Disjoint (X₁ : Set X') (X₂ : Set X') ∧
              X₁ ⊔ X₂ = ⊤ ∧
                (b ⁻¹ᵁ U) ≤ X₁ ∧
                  (b ⁻¹ᵁ V) ≤ X₂)
