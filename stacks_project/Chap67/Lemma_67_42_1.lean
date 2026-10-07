module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Quasi-compact morphisms satisfying existence are universally closed

A quasi-compact morphism of algebraic spaces that satisfies the existence part of
the valuative criterion is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- Lemma 67.42.1: If `f : X ⟶ Y` is a quasi-compact morphism of algebraic spaces
over a scheme `S` and `f` satisfies the existence part of the valuative criterion,
then `f` is universally closed. -/
@[stacks 03KA]
instance of_quasiCompact_of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [ValuativeCriterion.Existence f] :
    UniversallyClosed f :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
