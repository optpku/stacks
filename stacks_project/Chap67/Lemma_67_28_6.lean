module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Finite presentation morphisms into Noetherian algebraic spaces

A morphism of algebraic spaces of finite presentation into a Noetherian
target has Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FinitePresentation

/-- Lemma 67.28.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is of finite presentation and `Y` is
Noetherian, then `X` is Noetherian. -/
@[stacks 04ZL]
theorem isNoetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FinitePresentation f] [IsNoetherian Y] :
    IsNoetherian X :=
  sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicSpace
