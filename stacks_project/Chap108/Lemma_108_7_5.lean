module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_7_5_Map

/-!
# Lemma 108.7.5

A closed immersion of separated finite-presentation algebraic spaces over `B`
induces a closed immersion of Hilbert functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- Lemma 108.7.5: If `π : X ⟶ Y` is a closed immersion of algebraic spaces which
are separated and of finite presentation over an algebraic space `B`, then `π`
induces a closed immersion `closedMap π y : hilbert (π ≫ y) ⟶ hilbert y`. -/
@[stacks 0DPF]
theorem isClosedImmersion_map {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    Quot.IsClosedImmersionOnSchemesOver (closedMap π y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
