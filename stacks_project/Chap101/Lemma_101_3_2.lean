module

public import stacks_project.Chap101.Lemma_101_3_2_Group
public import stacks_project.Chap101.Lemma_101_3_2_Isom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 101.3.2

For an algebraic stack `X` and fibre objects `x, y` over a scheme `T`,
`Isom_X(y, y)` is a group algebraic space over `T`, and `Isom_X(x, y)` is a
pseudo torsor for that group space over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- Lemma 101.3.2 (1): `Isom_X(y, y)` is a group algebraic space over `T`. -/
@[stacks 04YP]
theorem automorphismGroup_X {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (y : X.p.Fiber T) :
    (automorphismGroup y).X = isomOver y y :=
  sorry

/-- Lemma 101.3.2 (2): `Isom_X(x, y)` is a pseudo torsor for `Isom_X(y, y)` over `T`. -/
@[stacks 04YP, instance]
instance instIsPseudoTorsor_action {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    Mod.IsPseudoTorsor (action x y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Isom
