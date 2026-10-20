/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Reduced
import StacksCheckRecall

/-!
# Reducedness of a proper flat algebraic space over a DVR

A proper flat algebraic space over the spectrum of a discrete valuation ring is
reduced as soon as its special fibre is reduced; the generic fibre is then
reduced as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.29.5 (1): Let `X` be an algebraic space over a discrete valuation
ring `R` whose structure morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))` is proper and flat.
If the special fibre `fiber f (IsLocalRing.closedPoint R)` is reduced, then `X`
is reduced. -/
@[stacks 0E0B] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_of_proper_flat_of_isReduced_specialFiber :
    ∀
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))],
    IsReduced X)

/- Lemma 76.29.5 (2): Let `X` be an algebraic space over a discrete valuation
ring `R` whose structure morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))` is proper and flat.
If the special fibre `fiber f (IsLocalRing.closedPoint R)` is reduced, then the
generic fibre `fiber f (genericPoint (Spec (CommRingCat.of R)))` is reduced. -/
@[stacks 0E0B] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_genericFiber_of_proper_flat_of_isReduced_specialFiber :
    ∀
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))],
    IsReduced (fiber f (genericPoint (Spec (CommRingCat.of R)))))
