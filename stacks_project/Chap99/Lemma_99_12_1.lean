module

import StacksCheckRecall
public import stacks_project.Chap99.Lemma_99_12_1_Mor
public import stacks_project.Chap99.Lemma_99_12_1_Graph

/-!
# Lemma 99.12.1

If `X ⟶ B` is separated and `Z ⟶ B` is of finite presentation, flat, and
proper, the graph of a `T`-morphism `Z_T ⟶ X_T` defines a natural injective
transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}` of functors on `(Sch/B)^op`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

/- Lemma 99.12.1 (1): there is a natural transformation
Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B} sending a morphism f : Z_T ⟶ X_T over T
to the class of its graph Γ_f ⊂ (Z ×_B X)_T. -/
@[stacks 0D1A] #check AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Lemma 99.12.1 (2): the graph transformation is injective on `T`-points: if
two morphisms `Z_T ⟶ X_T` over `T` have the same graph in `(Z ×_B X)_T`, then
they coincide. -/
@[stacks 0D1A]
theorem graph_app_injective {S : Scheme.{u}} {Z B X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] (σ : SchemesOver B) :
    Function.Injective fun b ↦ (graph z x).app (op σ) b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
