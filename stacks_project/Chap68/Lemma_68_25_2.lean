/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_25_2_DimensionFunction

/-!
# Dimension functions on decent algebraic spaces of finite type

A dimension function on a locally Noetherian universally catenary scheme
induces a dimension function on a decent algebraic space locally of finite
type over it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.25.2: If `S` is a locally Noetherian universally catenary scheme,
`δ : S → ℤ` is a dimension function, and `X` is a decent algebraic space over
`S` whose structure morphism `X ⟶ S` is locally of finite type, then
`relativeDimensionFunction X δ` is a dimension function on `Points X`. -/
@[stacks 0ED5]
instance instIsDimensionFunctionRelativeDimensionFunction {S : Scheme.{u}}
    (X : AlgebraicSpace S) [AlgebraicGeometry.UniversallyCatenary S]
    [LocallyOfFiniteType (toBase X)] [IsDecent X] (δ : S → ℤ)
    [IsDimensionFunction δ] :
    IsDimensionFunction (relativeDimensionFunction X δ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
