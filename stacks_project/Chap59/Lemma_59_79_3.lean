/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap59.Lemma_59_79_3_Sequence
public import stacks_project.Chap59.Lemma_59_79_3_Triangle

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry

universe u

/- Lemma 59.79.3 (1): the étale support triangle. -/
@[stacks 0A45] #check (AlgebraicGeometry.Scheme.Etale.Support.triangle_distinguished :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    Scheme.Etale.Support.triangle i F ∈ Pretriangulated.distinguishedTriangles)

/- Lemma 59.79.3 (2): the associated exact support sequence. -/
@[stacks 0A45] #check (AlgebraicGeometry.Scheme.Etale.Support.sequence_exact :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    (Scheme.Etale.Support.sequence i F).Exact)

/- Lemma 59.79.3 (3): the higher direct-image/support comparison. -/
@[stacks 0A45] #check (AlgebraicGeometry.Scheme.Etale.Support.higherDirectImageIso :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (degree : ℕ) (_ : 1 ≤ degree),
    ((Scheme.Etale.Abelian.directImage (closedImmersionComplement i).ι).rightDerived degree).obj
      ((Scheme.Etale.Abelian.inverseImage (closedImmersionComplement i).ι).obj F) ≅
    (Scheme.Etale.Abelian.directImage i).obj
      (((Scheme.Etale.Support.onClosed i).rightDerived (degree + 1)).obj F))
