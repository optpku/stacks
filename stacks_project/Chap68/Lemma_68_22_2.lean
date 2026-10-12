/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap68.Definition_68_22_1_Birational

/-!
# Birational morphisms of decent algebraic spaces are dominant

A birational morphism of decent algebraic spaces with finitely many irreducible
components is dominant.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Dominant

/-- Lemma 68.22.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which are decent and have finitely many irreducible components.
If `f` is birational then `f` is dominant. -/
@[stacks 0ACW]
instance of_isBirational {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] : Dominant f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Dominant
