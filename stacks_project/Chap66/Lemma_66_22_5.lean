module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Dimension of algebraic spaces is invariant under étale morphisms

An étale morphism of algebraic spaces preserves dimension at a point and the dimension of
the local ring at a point. If the morphism is surjective on points, it preserves global
dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Lemma 66.22.5 (1): let `S` be a scheme. Let `f : X ⟶ Y` be an étale morphism of algebraic
spaces over `S`. Let `x` be a point of `X`. Then `dimensionAt x = dimensionAt (Points.map f x)`. -/
@[stacks 0A4H]
theorem dimensionAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (x : Points X) :
    dimensionAt x = dimensionAt (Points.map f x) :=
  sorry

/-- Lemma 66.22.5 (2): let `S` be a scheme. Let `f : X ⟶ Y` be an étale morphism of algebraic
spaces over `S`. Let `x` be a point of `X`. Then the dimension of the local ring of `X` at `x`
equals the dimension of the local ring of `Y` at `Points.map f x`. -/
@[stacks 0A4H]
theorem localRingDimAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (x : Points X) :
    localRingDimAt x = localRingDimAt (Points.map f x) :=
  sorry

/-- Lemma 66.22.5 (3): let `S` be a scheme. Let `f : X ⟶ Y` be an étale morphism of algebraic
spaces over `S`. If `Points.map f` is surjective, then `dimension X = dimension Y`. -/
@[stacks 0A4H]
theorem dimension_eq_of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] (hf : Function.Surjective (Points.map f)) :
    dimension X = dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
