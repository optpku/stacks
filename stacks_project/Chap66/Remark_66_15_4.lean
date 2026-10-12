/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_12_8
public import stacks_project.Chap68.Lemma_68_14_2
public import stacks_project.Chap68.Lemma_68_15_2_David_Rydh
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Remark 66.15.4 (1): Lemma 66.15.3 holds for decent algebraic spaces via
Decent Spaces, Lemma 68.12.8. -/
@[stacks 03E0] #check exists_iso_spec_of_surjective_etale

/- Remark 66.15.4 (2): a decent algebraic space with one point is a scheme. -/
@[stacks 03E0] #check
  (IsScheme.of_singleton_points :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [Nonempty (Points X)] [Subsingleton (Points X)],
      IsScheme X)

/- Remark 66.15.4 (3): the preceding conclusions also apply when X is locally
separated because such an X is decent. -/
@[stacks 03E0] #check
  (instIsDecent_of_isAbsolutelyLocallySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsAbsolutelyLocallySeparated X], IsDecent X)
