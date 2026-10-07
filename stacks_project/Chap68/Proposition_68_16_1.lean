module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Valuative criterion for universal closedness of decent algebraic spaces

A quasi-compact morphism of algebraic spaces with decent source is universally
closed if and only if it satisfies the existence part of the valuative
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- Proposition 68.16.1: Let `f : X ⟶ Y` be a quasi-compact morphism of
algebraic spaces over a scheme `S`, and assume `X` is decent. Then `f` is
universally closed if and only if the existence part of the valuative
criterion holds. -/
@[stacks 03KJ]
theorem iff_existence_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [IsDecent X] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

end UniversallyClosed

namespace ValuativeCriterion.Existence

/-- If `f : X ⟶ Y` is a universally closed morphism of algebraic spaces over a
scheme `S` and the source `X` is decent, then `f` satisfies the existence part
of the valuative criterion. -/
theorem of_universallyClosed_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsDecent X] [UniversallyClosed f] : Existence f :=
  sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
