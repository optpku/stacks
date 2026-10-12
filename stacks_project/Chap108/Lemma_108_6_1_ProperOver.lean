/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap99.Proposition_99_8_4_Representable

/-!
# Proper functors of points over an algebraic space

A functor on `(Sch/B)ᵒᵖ` is proper over `B` when it is represented by a proper
morphism of algebraic spaces over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space proper over `B`. -/
def IsProperOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Proper π ∧ Nonempty (F ≅ yonedaOver π)

/-- Representability by an algebraic space proper over `B` is existence of a
proper morphism `π` together with an isomorphism to `yonedaOver π`. -/
theorem isProperOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsProperOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        Proper π ∧ Nonempty (F ≅ yonedaOver π) :=
  sorry

/-- Package a proper morphism over `B` and a representing isomorphism as
`IsProperOver`. -/
theorem IsProperOver.of {X : AlgebraicSpace S} {π : X ⟶ B} (hProper : Proper π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    IsProperOver F :=
  sorry

/-- `IsProperOver.of` records properness of `π` and the given representing
isomorphism. -/
theorem IsProperOver.of_spec {X : AlgebraicSpace S} {π : X ⟶ B}
    (hProper : Proper π) {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ yonedaOver π) :
    Proper π ∧ Nonempty (F ≅ yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
