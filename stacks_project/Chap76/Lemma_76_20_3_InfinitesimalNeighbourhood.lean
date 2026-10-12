/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Smoothness and étaleness from infinitesimal neighbourhoods

If every base change of a locally finite-type morphism of algebraic spaces to
an infinitesimal neighbourhood of a closed subspace of a locally Noetherian
target is smooth (resp. étale), then the morphism is smooth (resp. étale) at
every point lying above that closed subspace.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood

/-- If every base change of a locally finite-type morphism of algebraic spaces
to an infinitesimal neighbourhood of a closed subspace of a locally Noetherian
target is smooth, then the morphism is smooth at every point lying above that
closed subspace. -/
theorem smoothAt_of_smooth_pullbacks {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    [∀ n : ℕ, Smooth (pullback.snd f (toAmbient i n))]
    (x : Points X) (hx : Points.map f x ∈ Set.range (Points.map i)) :
    SmoothAt f x :=
  sorry

/-- If every base change of a locally finite-type morphism of algebraic spaces
to an infinitesimal neighbourhood of a closed subspace of a locally Noetherian
target is étale, then the morphism is étale at every point lying above that
closed subspace. -/
theorem etaleAt_of_etale_pullbacks {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    [∀ n : ℕ, Etale (pullback.snd f (toAmbient i n))]
    (x : Points X) (hx : Points.map f x ∈ Set.range (Points.map i)) :
    EtaleAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood
