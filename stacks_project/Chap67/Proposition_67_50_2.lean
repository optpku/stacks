module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Representability of separated locally quasi-finite algebraic spaces

A separated, locally quasi-finite morphism of algebraic spaces over a scheme
with representable target has representable source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Proposition 67.50.2: Let `S` be a scheme. Let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`. If `T` is representable, `f` is locally quasi-finite,
and `f` is separated, then `X` is representable. -/
@[stacks 03XX]
theorem of_locallyQuasiFinite_separated {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [IsScheme T] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [Separated f] : IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
