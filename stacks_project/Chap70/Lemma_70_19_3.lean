/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.IsoOverOpen.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.MeromorphicSection

/-!
# Equivalence of modifications after base change to the henselization

For a decent algebraic space, finite-presentation morphisms that are
isomorphisms away from a closed point with quasi-compact complement are
equivalent, after base change, to the corresponding morphisms over the
punctured henselization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.19.3: Base change to a henselization at a closed point with
quasi-compact complement gives an equivalence on finite-presentation modifications. -/
@[stacks 0BH0] #check
  (AlgebraicGeometry.AlgebraicSpace.puncturedHenselizationBaseChange_isEquivalence :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)] (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R],
    (puncturedHenselizationBaseChange X hx N hN R).IsEquivalence)

end AlgebraicGeometry.AlgebraicSpace
