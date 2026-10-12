/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Definition_68_22_1_Birational

/-!
# Dense open restrictions of birational morphisms of algebraic spaces

A birational morphism of decent algebraic spaces with finitely many
irreducible components becomes an isomorphism between dense opens after
restriction, provided it is locally of finite type with reduced target, or
locally of finite presentation.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- Lemma 68.22.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a birational morphism
of algebraic spaces over `S` which are decent and have finitely many
irreducible components. Assume either `f` is locally of finite type and `Y` is
reduced, or `f` is locally of finite presentation. Then there exist dense opens
`U ⊂ X` and `V ⊂ Y` such that `f(U) ⊂ V` and `f|_U : U ⟶ V` is an
isomorphism. -/
@[stacks 0BBE]
theorem exists_dense_opens_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f]
    (h : (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  sorry

/-- A birational morphism that is locally of finite type onto a reduced target
restricts to an isomorphism between dense opens. -/
theorem exists_dense_opens_isIso_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFiniteType f] [IsReduced Y] :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  sorry

/-- A birational morphism that is locally of finite presentation restricts to
an isomorphism between dense opens. -/
theorem exists_dense_opens_isIso_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] [LocallyOfFinitePresentation f] :
    ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (φ : U.X ⟶ V.X),
      Dense U.pointsSet ∧ Dense V.pointsSet ∧
        φ ≫ V.ι = U.ι ≫ f ∧ IsIso φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational
