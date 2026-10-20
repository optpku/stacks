module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BaseChange.Completion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackConditions
public import ReasLib.RingTheory.AdicCompletion.LocalMap

/-!
# Completions of henselian local rings after base change to the completion
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a local ring with finitely generated maximal ideal and a decent algebraic
space over its spectrum, base change to the maximal-ideal-adic completion induces
a bijection on completions of henselian local rings at every point whose image
lies over the closed point. The comparison map is induced by the first projection. -/
theorem completionHenselianLocalRingMap_bijective_of_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A] (hfg : (maximalIdeal A).FG)
    (X : AlgebraicSpace (Spec (.of A))) [IsDecent X]
    (q : Points (completionBaseChange A X))
    (hq : Points.base (Points.map (completionBaseChange.fst A X) q) =
      closedPoint A) :
    Function.Bijective
      (AdicCompletion.mapLocal
        (HenselianFunctoriality.map (completionBaseChange.fst A X) q
          (Points.map (completionBaseChange.fst A X) q) rfl)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
