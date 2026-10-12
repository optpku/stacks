/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap81.Lemma_81_14_7_Compactification

/-!
# Lemma 81.14.7

Compactifications of the legs of an elementary distinguished square glue to a
compactification of the vertex, over a finite-type base over `ℤ`, when the
fibre product of the legs is dense in the vertex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasCompactification

/-- Lemma 81.14.7. Let `B` be an algebraic space of finite type over `ℤ`. Let
`U` be an algebraic space of finite type and separated over `B`. Let
`(j : U2 ⟶ U, f : U1 ⟶ U)` be an elementary distinguished square. If `U1` and
`U2` have compactifications over `B` and `U1 ×_U U2 ⟶ U` has dense image, then
`U` has a compactification over `B`. -/
@[stacks 0F4B]
theorem of_isElementaryDistinguishedSquare
    {B U U1 U2 : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    [FiniteType (toBase B)] (fU : U ⟶ B) [FiniteType fU] [Separated fU]
    (j : U2 ⟶ U) (f : U1 ⟶ U) [IsElementaryDistinguishedSquare j f]
    [HasCompactification (j ≫ fU)] [HasCompactification (f ≫ fU)]
    (h_dense : Dense (Set.range (Points.map (pullback.fst j f ≫ j)))) :
    HasCompactification fU :=
  sorry

end HasCompactification

end AlgebraicGeometry.AlgebraicSpace
