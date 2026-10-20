module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Projective.Modification
import StacksCheckRecall

/-!
# Modifications of complete 2-dimensional local domains

A modification of the spectrum of a complete Noetherian local domain of
dimension 2 is a scheme H-projective over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 89.2.4 If `(A, 𝔪, κ)` is a complete Noetherian local domain of
 dimension `2`, then every modification of `Spec(A)` is projective over `A`. -/
@[stacks 0AGN] #check
  (AlgebraicGeometry.AlgebraicSpace.isScheme_hProjective_of_isModification :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
      [IsCompleteLocalRing A], ringKrullDim A = 2 →
      ∀ {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X]
        [IsIntegral (specSpace A)] (f : X ⟶ specSpace A) [IsModification f],
        ∃ (T : Over (Spec (.of A))),
          Nonempty (X ≅ ofOver T) ∧ HProjective T.hom)

end AlgebraicGeometry.AlgebraicSpace
