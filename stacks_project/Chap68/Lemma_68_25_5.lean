/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary

/-!
# Locally of finite type over universally catenary algebraic spaces

A decent algebraic space locally of finite type over a universally catenary
algebraic space is itself universally catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.25.5: Let `S` be a scheme. Let `X` be a decent, locally Noetherian,
and universally catenary algebraic space over `S`. Then any decent algebraic
space locally of finite type over `X` is universally catenary. -/
@[stacks 0ED8]
theorem universallyCatenary_of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [UniversallyCatenary X]
    [LocallyOfFiniteType f] [IsDecent Y] : UniversallyCatenary Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
