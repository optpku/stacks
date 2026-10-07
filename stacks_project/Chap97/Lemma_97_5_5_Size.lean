module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Size of algebraic spaces

An algebraic space over a scheme `S` has size at most a cardinal `κ` when it
admits a surjective étale presentation by a scheme of size at most `κ`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space `X` over `S` has size at most `κ` if there exists a scheme
`U` over `S` with `U.left.size ≤ κ` and a surjective étale morphism
`ofOver U ⟶ X`. -/
def sizeLE (κ : Cardinal.{u}) {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∃ (U : Over S) (p : ofOver U ⟶ X), Etale p ∧ Surjective p ∧ U.left.size ≤ κ

/-- Unfolding of `sizeLE`: a surjective étale atlas by a scheme of size at most
`κ`. -/
theorem sizeLE_iff (κ : Cardinal.{u}) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    sizeLE κ X ↔
      ∃ (U : Over S) (p : ofOver U ⟶ X), Etale p ∧ Surjective p ∧ U.left.size ≤ κ :=
  sorry

namespace sizeLE

/-- A surjective étale presentation by a scheme of size at most `κ` witnesses
`sizeLE κ X`. -/
theorem of {κ : Cardinal.{u}} {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) [Etale p] [Surjective p] (hU : U.left.size ≤ κ) :
    sizeLE κ X :=
  sorry

end sizeLE

/-- A scheme `U` over `S` of size at most `κ`, viewed as an algebraic space, has
size at most `κ`. -/
theorem sizeLE_ofOver {κ : Cardinal.{u}} {S : Scheme.{u}} {U : Over S}
    (hU : U.left.size ≤ κ) : sizeLE κ (ofOver U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
