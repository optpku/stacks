module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Valuative criterion for universal closedness of decent morphisms

A quasi-compact decent morphism of algebraic spaces is universally closed if
and only if it satisfies the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- Lemma 68.17.11: Let `f : X ⟶ Y` be a quasi-compact and decent morphism of
algebraic spaces over a scheme `S`. (For example if `f` is representable, or
quasi-separated, see Lemma 68.17.2.) Then `f` is universally closed if and only
if the existence part of the valuative criterion holds. -/
@[stacks 03M6]
theorem iff_existence_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [Decent f] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

end UniversallyClosed

namespace ValuativeCriterion.Existence

/-- If `f : X ⟶ Y` is a quasi-compact universally closed decent morphism of
algebraic spaces over a scheme `S`, then `f` satisfies the existence part of
the valuative criterion. -/
theorem of_universallyClosed_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [Decent f] [UniversallyClosed f] : Existence f :=
  sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
