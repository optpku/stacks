/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.Lemma_78_19_4_Representability

/-!
# Covering properties of groupoid quotients in algebraic spaces

If `(U, R, s, t, c)` is a groupoid in algebraic spaces whose source and target
are flat and locally of finite presentation, and `j = (t, s)` is an
equivalence relation, then a morphism `U ⟶ F` representing `F = U / R` is
surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {F : AlgebraicSpace S} (q : G.U.left ⟶ F)
variable (h_equalizes : G.toPreRelation.t.left ≫ q = G.toPreRelation.s.left ≫ q)
variable [IsEquivalenceRelation G.t G.s]
variable [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
variable [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
variable [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
variable [IsIso (G.toPreRelation.quotientSheafDesc q h_equalizes)]

/-- Lemma 80.11.6 (1): let `S` be a scheme. Consider an algebraic space `F` of
the form `F = U / R` where `(U, R, s, t, c)` is a groupoid in algebraic spaces
over `S` such that `s, t` are flat and locally of finite presentation, and
`j = (t, s) : R ⟶ U ⨯ U` is an equivalence relation. Then a morphism `q : U ⟶ F`
representing the quotient is surjective. -/
@[stacks 06PG]
instance quotientHom_surjective : AlgebraicSpace.Surjective q := sorry

/-- Lemma 80.11.6 (2): let `S` be a scheme. Consider an algebraic space `F` of
the form `F = U / R` where `(U, R, s, t, c)` is a groupoid in algebraic spaces
over `S` such that `s, t` are flat and locally of finite presentation, and
`j = (t, s) : R ⟶ U ⨯ U` is an equivalence relation. Then a morphism `q : U ⟶ F`
representing the quotient is flat. -/
@[stacks 06PG]
instance quotientHom_flat : AlgebraicSpace.Flat q := sorry

/-- Lemma 80.11.6 (3): let `S` be a scheme. Consider an algebraic space `F` of
the form `F = U / R` where `(U, R, s, t, c)` is a groupoid in algebraic spaces
over `S` such that `s, t` are flat and locally of finite presentation, and
`j = (t, s) : R ⟶ U ⨯ U` is an equivalence relation. Then a morphism `q : U ⟶ F`
representing the quotient is locally of finite presentation. -/
@[stacks 06PG]
instance quotientHom_locallyOfFinitePresentation :
    AlgebraicSpace.LocallyOfFinitePresentation q := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
