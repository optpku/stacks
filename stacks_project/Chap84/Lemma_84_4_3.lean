module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ProperHenselian

/-!
# Lemma 84.4.3

For a proper algebraic space over a henselian local ring, restriction
identifies global sections of any sheaf of sets on the small étale site
with those of its inverse image on the closed fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 84.4.3: if `A` is a henselian local ring and `X` is an algebraic space
over `Spec A` whose structure morphism is proper, then for the inclusion of the
fibre `X₀` of `SchemeRealization.toBase X` over the closed point (equivalently the special fibre
at `I = IsLocalRing.maximalIdeal A`), restriction identifies `Γ(X, F)` with
`Γ(X₀, F|_{X₀})` for every sheaf of sets `F` on `X_étale`. -/
@[stacks 0DFZ] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleGlobalSections_bijective_of_properHenselianLocal :
    ∀ {A : Type u} [CommRing A] [HenselianLocalRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [Proper (SchemeRealization.toBase X)]
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    Function.Bijective
      (smallEtaleGlobalSectionsPullback
        (pullback.fst (SchemeRealization.toBase X)
          (specQuotientι (IsLocalRing.maximalIdeal A))) F))

end AlgebraicGeometry.AlgebraicSpace
