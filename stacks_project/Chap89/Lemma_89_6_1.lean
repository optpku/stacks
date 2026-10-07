module

public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import stacks_project.Chap89.Lemma_89_6_1_BaseChange
public import stacks_project.Chap89.Lemma_89_6_1_HenselianMap

/-!
# Completions of henselian local rings after base change to the completion
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.6.1: Let `(A, m, κ)` be a local ring with finitely generated maximal
ideal `m`. Let `X` be a decent algebraic space over `A`. Let
`Y = completionBaseChange A X` be the base change of `X` to `Spec` of the
`m`-adic completion of `A`. For a point `q` of `Y` whose image
`p = Points.map (completionBaseChange.fst A X) q` in `X` lies over the closed
point of `Spec(A)`, the map `henselianLocalRing.baseChangeHom q` of henselian
local rings `henselianLocalRing X p ⟶ henselianLocalRing Y q` induces an
isomorphism on maximal-ideal-adic completions. -/
@[stacks 0BHP]
theorem completionHenselianLocalRingMap_bijective_of_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A] (hfg : (maximalIdeal A).FG)
    (X : AlgebraicSpace (Spec (.of A))) [IsDecent X]
    (q : Points (completionBaseChange A X))
    (hq : Points.base (Points.map (completionBaseChange.fst A X) q) =
      closedPoint A) :
    Function.Bijective
      (AdicCompletion.mapLocal (henselianLocalRing.baseChangeHom q)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
