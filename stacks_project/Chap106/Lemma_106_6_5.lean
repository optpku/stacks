module

public import stacks_project.Chap106.«106_6_1_1_Object»
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Étale-local cartesian smooth lifts along thickenings

A smooth morphism from an algebraic space to a thickening of algebraic stacks
admits an étale covering by 2-cartesian smooth lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- Lemma 106.6.5. Let `iX : X ⟶ X'` be a thickening of algebraic stacks. Let
`W` be an algebraic space and let `x : W.toGroupoids ⟶ X` be a smooth
morphism. There exists an étale covering `{Wi ⟶ W}` and, for each `i`, a
2-cartesian square `Wi ⟶ Wi'` over `X ⟶ X'` with `Wi' ⟶ X'` smooth.

The covering arrows are `(ξ i).a : (ξ i).U ⟶ W`, the top arrows of the
squares are `(ξ i).i : (ξ i).U ⟶ (ξ i).U'`, the smooth maps `Wi' ⟶ X'` are
`(ξ i).x'`, and the square 2-cells are `(ξ i).α`. -/
@[stacks 0CJV]
theorem exists_etaleCovering {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    ∃ (ι : Type u) (ξ : ι → Object iX x),
      AlgebraicSpace.EtaleCovering (fun i ↦ Over.mk (ξ i |>.a)) :=
  sorry

/-- An étale covering by lift objects consists of étale maps `a`, smooth maps
`x'`, 2-cartesian cones, and a jointly surjective family on points of `W`. -/
theorem exists_etaleCovering_spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x] :
    ∃ (ι : Type u) (ξ : ι → Object iX x),
      (∀ i, AlgebraicSpace.Etale (ξ i).a) ∧
        (∀ i, Groupoids.Hom.Smooth (ξ i).x') ∧
        (∀ i, Bicategory.PseudoPullbackCone.IsBilimit (ξ i).cone) ∧
        (⋃ i, Set.range (AlgebraicSpace.Points.map (ξ i).a)) = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Lift
