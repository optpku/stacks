/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap68.Definition_68_25_1_Catenary
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Catenary decent algebraic spaces of finite type

A decent algebraic space locally of finite type over a locally Noetherian
universally catenary scheme is catenary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.25.3: If `S` is a locally Noetherian universally catenary scheme
and `X` is a decent algebraic space over `S` whose structure morphism `X ⟶ S`
is locally of finite type, then `X` is catenary. -/
@[stacks 0ED6]
instance instIsCatenary_of_locallyOfFiniteType {S : Scheme.{u}}
    (X : AlgebraicSpace S) [AlgebraicGeometry.UniversallyCatenary S]
    [LocallyOfFiniteType (toBase X)] [IsDecent X] :
    IsCatenary X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
