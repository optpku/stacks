module

public import stacks_project.Chap101.Lemma_101_23_6_Covering

/-!
# Covering characterizations of quasi-DM morphisms of algebraic stacks

A morphism of algebraic stacks is quasi-DM if and only if every algebraic-space
test of the target has a locally quasi-finite flat algebraic-space cover of the
2-fibre product, and if and only if some fppf algebraic-space cover of the
target has such a cover of the 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiDM

/-- Lemma 101.23.6 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-DM if and only if for every algebraic space `V` and morphism
`g : V.toGroupoids ⟶ Y` there exists a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from an algebraic space to
`TwoFibreProduct.apex f g`, i.e. informally `X ×_Y V`. -/
@[stacks 06UE]
theorem iff_existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    QuasiDM f ↔ existsCoverOnPullbacks f :=
  sorry

/-- Lemma 101.23.6 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-DM if and only if there exist algebraic spaces `U`, `V` with a
surjective, flat, locally of finite presentation morphism
`g : V.toGroupoids ⟶ Y` and a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from `U` to
`TwoFibreProduct.apex f g`. -/
@[stacks 06UE]
theorem iff_existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    QuasiDM f ↔ existsCoverOverFppf f :=
  sorry

/-- A quasi-DM morphism of algebraic stacks admits a locally quasi-finite
flat algebraic-space cover of every 2-fibre product against an algebraic
space over the target. -/
theorem existsCoverOnPullbacks_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiDM f] :
    existsCoverOnPullbacks f :=
  sorry

/-- The covering criterion on every algebraic-space test of the target implies
that a morphism of algebraic stacks is quasi-DM. -/
theorem of_existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : existsCoverOnPullbacks f) : QuasiDM f :=
  sorry

/-- A quasi-DM morphism of algebraic stacks admits some fppf algebraic-space
cover of the target whose 2-fibre product has a locally quasi-finite flat
algebraic-space cover. -/
theorem existsCoverOverFppf_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiDM f] :
    existsCoverOverFppf f :=
  sorry

/-- An fppf algebraic-space cover of the target together with a locally
quasi-finite flat algebraic-space cover of the 2-fibre product implies that a
morphism of algebraic stacks is quasi-DM. -/
theorem of_existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : existsCoverOverFppf f) : QuasiDM f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiDM
