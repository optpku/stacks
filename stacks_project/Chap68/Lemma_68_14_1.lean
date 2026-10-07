module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Locally Noetherian decent algebraic spaces are quasi-separated

A locally Noetherian decent algebraic space is quasi-separated in the absolute
sense of Properties of Spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelyQuasiSeparated

/-- Lemma 68.14.1: Any locally Noetherian decent algebraic space is quasi-separated. -/
@[stacks 0BB6]
instance of_isLocallyNoetherian_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsDecent X] :
    IsAbsolutelyQuasiSeparated X := sorry

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
