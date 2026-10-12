/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_5_3_Aut
public import stacks_project.Chap101.Definition_101_5_3_Group
public import stacks_project.Chap101.Definition_101_5_3_Isom
import StacksCheckRecall

@[expose] public section

/- Definition 101.5.3 (1): for a morphism `f : X ⟶ Y` of algebraic stacks and
a morphism `x : Z ⟶ X` from an algebraic space, the relative sheaf of
automorphisms of `x` is the 2-fibre product `Z ×_{x, X} I_{X/Y}`. -/
@[stacks 06PP] #check AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeAut

/- Definition 101.5.3 (1): the relative automorphism sheaf is a group
algebraic space over `Z` by pullback of the composition law of
Remark 101.5.2. -/
@[stacks 06PP] #check AlgebraicGeometry.AlgebraicStack.RelativeIsom.instGrpObj_asHomotopy

/- Definition 101.5.3 (2): for morphisms `x1, x2 : Z ⟶ X` and a 2-morphism
`α : f ∘ x1 ⟶ f ∘ x2`, the relative sheaf of isomorphisms from `x1` to `x2`
is `(Z ×_X Z) ×_{Z ×_Y Z, Δ^α} Z`. -/
@[stacks 06PP] #check AlgebraicGeometry.AlgebraicStack.RelativeIsom.relativeIsom

/- Definition 101.5.3 (3): if `Y` is the identity fibration over `S`, the
relative automorphism sheaf is written `Isom_X(x, x)`. -/
@[stacks 06PP] #check AlgebraicGeometry.AlgebraicStack.RelativeIsom.aut

/- Definition 101.5.3 (3): if `Y` is the identity fibration over `S`, the
relative isomorphism sheaf is written `Isom_X(x1, x2)`. -/
@[stacks 06PP] #check AlgebraicGeometry.AlgebraicStack.RelativeIsom.isom
