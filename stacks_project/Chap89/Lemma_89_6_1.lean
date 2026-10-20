module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Completion

/-!
# Completions of henselian local rings after base change to the completion
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 89.6.1: Base change to the maximal-ideal-adic completion of a local ring
with finitely generated maximal ideal induces an isomorphism on completions of
henselian local rings over the closed point of the base. -/
@[stacks 0BHP] #check
  (AlgebraicGeometry.AlgebraicSpace.completionHenselianLocalRingMap_bijective_of_baseChange :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] (hfg : (maximalIdeal A).FG)
      (X : AlgebraicSpace (Spec (.of A))) [IsDecent X]
      (q : Points (completionBaseChange A X))
      (hq : Points.base (Points.map (completionBaseChange.fst A X) q) =
        closedPoint A),
      Function.Bijective
        (AdicCompletion.mapLocal
          (HenselianFunctoriality.map (completionBaseChange.fst A X) q
            (Points.map (completionBaseChange.fst A X) q) rfl)))

end AlgebraicGeometry.AlgebraicSpace
