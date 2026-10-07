module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Compactification

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 33.43.9 (1): a regular curve over a field admits a regular projective compactification
whose complement is a finite set of closed points. -/
@[stacks 0H1F] #check
  (AlgebraicGeometry.Curve.exists_regularProjectiveCompactification :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left],
      ∃ (Xbar : Over (Spec (CommRingCat.of k))) (j : X.left ⟶ Xbar.left)
        (hj : IsOpenImmersion j),
        let U : Xbar.left.Opens := @Scheme.Hom.opensRange _ _ j hj
        j ≫ Xbar.hom = X.hom ∧
          Curve Xbar ∧
          Scheme.Regular Xbar.left ∧
          Projective Xbar.hom ∧
          Set.Finite ((U : Set Xbar.left)ᶜ) ∧
          ∀ x ∈ ((U : Set Xbar.left)ᶜ), x ∈ closedPoints Xbar.left)

/- Remark 33.43.9 (2): a regular curve over a perfect field is smooth over that field. -/
@[stacks 0H1F] #check
  (AlgebraicGeometry.Curve.smooth_of_regular_of_perfectField :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left] [PerfectField k],
      Smooth X.hom)

/- Remark 33.43.9 (3): a regular curve over a perfect field admits a smooth regular projective
compactification whose complement is a finite set of closed points. -/
@[stacks 0H1F] #check
  (AlgebraicGeometry.Curve.exists_smoothProjectiveCompactification_of_regular_of_perfectField :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left] [PerfectField k],
      ∃ (Xbar : Over (Spec (CommRingCat.of k))) (j : X.left ⟶ Xbar.left)
        (hj : IsOpenImmersion j),
        let U : Xbar.left.Opens := @Scheme.Hom.opensRange _ _ j hj
        j ≫ Xbar.hom = X.hom ∧
          Curve Xbar ∧
          Scheme.Regular Xbar.left ∧
          Projective Xbar.hom ∧
          Smooth Xbar.hom ∧
          Set.Finite ((U : Set Xbar.left)ᶜ) ∧
          ∀ x ∈ ((U : Set Xbar.left)ᶜ), x ∈ closedPoints Xbar.left)
