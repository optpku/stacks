/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ProperHenselian

/-!
# Lemma 84.4.2

For a proper algebraic space over a henselian pair, restriction identifies
global sections of any sheaf of sets on the small étale site with those of
its inverse image on the special fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 84.4.2: if `(A, I)` is a henselian pair and `X` is an algebraic space
over `Spec A` whose structure morphism is proper, then for the inclusion `i` of
the special fibre `X ×_{Spec A} Spec(A / I)` into `X`, restriction identifies
`Γ(X, F)` with `Γ(X₀, i⁻¹ F)` for every sheaf of sets `F` on `X_étale`. -/
@[stacks 0DFY] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleGlobalSections_bijective_of_properHenselianPair :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [Proper (SchemeRealization.toBase X)]
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    Function.Bijective
      (smallEtaleGlobalSectionsPullback
        (pullback.fst (SchemeRealization.toBase X) (specQuotientι I)) F))

end AlgebraicGeometry.AlgebraicSpace
