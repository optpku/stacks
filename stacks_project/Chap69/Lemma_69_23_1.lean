module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_5_DiscreteFiber

/-!
# Finite morphisms of algebraic spaces over a locally Noetherian target

A morphism of algebraic spaces over a locally Noetherian target is finite if
and only if it is proper and has discrete field fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsFinite

/-- Lemma 69.23.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is locally Noetherian. Then `f` is
finite if and only if `f` is proper and every field fibre is discrete, i.e.
`discreteFieldFibers f`. A more general version without local Noetherianity
is Lemma 76.35.1. -/
@[stacks 0A4V]
theorem iff_proper_and_discreteFieldFibers_of_isLocallyNoetherian
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) : IsFinite f ↔ Proper f ∧ discreteFieldFibers f :=
  sorry

/-- A proper morphism of algebraic spaces over a locally Noetherian target,
with discrete field fibres, is finite. -/
theorem of_proper_of_discreteFieldFibers {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (h : discreteFieldFibers f) : IsFinite f :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
