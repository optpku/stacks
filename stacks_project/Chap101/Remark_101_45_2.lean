module

public import stacks_project.Chap101.Lemma_101_6_6_Isom
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Inertia comparison along a morphism of algebraic stacks

For `f : X ⟶ Y` and a map `x : U ⟶ X` from an algebraic space, the
pullback `G ⟶ H` of `I_X ⟶ X ×_Y I_Y` to `U` is the Isom comparison
`isomComparison f x x`. Scheme-slice morphism properties of `Δ_f` pass to
this comparison, as in Lemma 101.6.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Remark 101.45.2: let `f : X ⟶ Y` be a morphism of algebraic stacks and let
`x : U ⟶ X` be a morphism whose source is an algebraic space. The pullback
`G ⟶ H` of `I_X ⟶ X ×_Y I_Y` to `U` is the inertia comparison
`isomComparison f x x`. If `Δ_f` has a scheme-slice morphism property `P`
(unramified, étale, etc.), so does `G ⟶ H`. This holds because
`fibreProductComparison f x x : U ×_X U ⟶ U ×_Y U` is cartesian over
`Hom.diagonal f`, and `isomComparison f x x` is the further base change of
that left vertical arrow by `Δ_U`, as in Lemma 101.6.6. -/
@[stacks 0DU8]
theorem inertiaComparison_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {U : AlgebraicSpace S}
    (x : U.toGroupoids ⟶ X) (P : MorphismProperty (AlgebraicSpace S))
    (hP : Groupoids.Hom.has P (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has P (isomComparison f x x) :=
  sorry

/-- If the relative 2-diagonal of `f` is unramified, then so is the inertia
comparison `isomComparison f x x`. -/
theorem inertiaComparison_unramified {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {U : AlgebraicSpace S}
    (x : U.toGroupoids ⟶ X)
    (hP : Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (isomComparison f x x) :=
  sorry

/-- If the relative 2-diagonal of `f` is étale, then so is the inertia
comparison `isomComparison f x x`. -/
theorem inertiaComparison_etale {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {U : AlgebraicSpace S}
    (x : U.toGroupoids ⟶ X)
    (hP : Groupoids.Hom.has (@AlgebraicSpace.Etale S)
      (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has (@AlgebraicSpace.Etale S) (isomComparison f x x) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
