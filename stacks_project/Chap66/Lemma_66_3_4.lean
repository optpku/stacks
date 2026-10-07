module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_3_4_Pullback

/-!
# Characterizations of absolutely separated algebraic spaces

Lemma 66.3.4 records that absolute separatedness of an algebraic space is equivalent to
affineness of fibre products of morphisms from affine schemes, together with surjectivity of the
induced `ℤ`-tensor map on global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelySeparated

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Lemma 66.3.4: let `S` be a scheme and `X` an algebraic space over `S`. The following are
equivalent: `X` is a separated algebraic space; for morphisms `U ⟶ X` and `V ⟶ X` from affine
schemes, the fibre product `U ×_X V` is affine and
`Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)` is surjective. -/
@[stacks 0AHS]
theorem tfae : List.TFAE [IsAbsolutelySeparated X, forallAffinePullbackAffineSurjective X] :=
  sorry

/-- An algebraic space is absolutely separated iff fibre products of morphisms from affine schemes
are affine with surjective tensor map on global sections. -/
theorem iff_forallAffinePullbackAffineSurjective :
    IsAbsolutelySeparated X ↔ forallAffinePullbackAffineSurjective X :=
  sorry

/-- An algebraic space is absolutely separated iff fibre products of morphisms from affine schemes
induce a closed immersion into the absolute product of the underlying schemes. -/
theorem iff_forallAffinePullbackClosedImmersion :
    IsAbsolutelySeparated X ↔ forallAffinePullbackClosedImmersion X :=
  sorry

end IsAbsolutelySeparated

end AlgebraicGeometry.AlgebraicSpace
