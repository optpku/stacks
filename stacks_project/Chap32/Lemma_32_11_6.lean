module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.IntegralAlgebra
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.11.6: an ample invertible module admits an affine nonvanishing open contained in
a prescribed open and through which a morphism from the spectrum of an integral algebra over
a field factors. -/
@[stacks 0E21] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.exists_affineNonvanishingOpen_factorization_of_isIntegral :
    ∀ {X : Scheme.{u}} {L : X.Modules} [hL : Scheme.Modules.Invertible L]
      [Scheme.Modules.IsAmple L],
      (W : X.Opens) → (k A : Type u) → [Field k] → [CommRing A] →
        [Algebra k A] → [Algebra.IsIntegral k A] →
          (toW : Spec (CommRingCat.of A) ⟶ W.toScheme) →
            ∃ n : ℕ+,
              ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
                ∃ _ : IsAffineOpen (hL.nonvanishingOpen s),
                  ∃ hsub : hL.nonvanishingOpen s ≤ W,
                    ∃ lift : Spec (CommRingCat.of A) ⟶
                        (hL.nonvanishingOpen s).toScheme,
                      lift ≫ X.homOfLE hsub = toW)
