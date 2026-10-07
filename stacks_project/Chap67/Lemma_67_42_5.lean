module

public import stacks_project.Chap67.Lemma_67_42_5_Along
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Refined valuative criterion for universal closedness

A quasi-compact morphism of algebraic spaces that satisfies uniqueness and
existence of the valuative criterion along a quasi-compact dominant morphism is
universally closed, and is separated if it is moreover quasi-separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Along

/-- Lemma 67.42.5 (1): Let `S` be a scheme, and let `f : X ⟶ Y` and `h : U ⟶ X`
be quasi-compact morphisms of algebraic spaces over `S`. If `|h|(|U|)` is dense
in `|X|`, every valuative solid square whose generic arrow factors through `h`
has at most one dotted lift `Spec(A) ⟶ X`, and every such square admits a
dominating valuation-ring extension with a morphism `Spec(A') ⟶ X` filling the
extended diagram, then `f` is universally closed. -/
@[stacks 089G]
theorem universallyClosed {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [QuasiCompact f] [QuasiCompact h] [Dominant h]
    (h_uniqueness : Uniqueness h f) (h_existence : Existence h f) :
    UniversallyClosed f :=
  sorry

/-- Lemma 67.42.5 (2): Under the hypotheses of Lemma 67.42.5 (1), if moreover
`f` is quasi-separated, then `f` is separated. -/
@[stacks 089G]
theorem separated {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (h : U ⟶ X) [QuasiCompact f] [QuasiCompact h] [Dominant h] [QuasiSeparated f]
    (h_uniqueness : Uniqueness h f) (h_existence : Existence h f) :
    Separated f :=
  sorry

end ValuativeCriterion.Along

end AlgebraicGeometry.AlgebraicSpace
