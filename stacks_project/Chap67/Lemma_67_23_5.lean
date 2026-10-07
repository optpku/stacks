module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Locally of finite type over locally Noetherian algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 67.23.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type and `Y` is
locally Noetherian, then `X` is locally Noetherian. -/
@[stacks 04ZK]
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
