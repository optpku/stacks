/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap71.Lemma_71_15_2_Fiber

/-!
# Reducedness of a proper flat algebraic space over a DVR

A proper flat algebraic space over the spectrum of a discrete valuation ring is
reduced as soon as its special fibre is reduced; the generic fibre is then
reduced as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.29.5 (1): Let `X` be an algebraic space over a discrete valuation
ring `R` whose structure morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))` is proper and flat.
If the special fibre `fiber f (IsLocalRing.closedPoint R)` is reduced, then `X`
is reduced. -/
@[stacks 0E0B]
theorem isReduced_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))] :
    IsReduced X :=
  sorry

/-- Lemma 76.29.5 (2): Let `X` be an algebraic space over a discrete valuation
ring `R` whose structure morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))` is proper and flat.
If the special fibre `fiber f (IsLocalRing.closedPoint R)` is reduced, then the
generic fibre `fiber f (genericPoint (Spec (CommRingCat.of R)))` is reduced. -/
@[stacks 0E0B]
theorem isReduced_genericFiber_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))] :
    IsReduced (fiber f (genericPoint (Spec (CommRingCat.of R)))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
