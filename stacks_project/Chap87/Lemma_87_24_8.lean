module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Locally of finite type over locally Noetherian formal algebraic spaces

A morphism of formal algebraic spaces that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 87.24.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. If `Y` is locally Noetherian and `f` is
locally of finite type, then `X` is locally Noetherian. -/
@[stacks 0AQ7]
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
