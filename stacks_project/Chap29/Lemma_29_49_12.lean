/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.OpenSubschemes
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

#check (AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemes :
  AlgebraicGeometry.Scheme → AlgebraicGeometry.Scheme → Prop)

#check (AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemesOver :
  ∀ (S X Y : AlgebraicGeometry.Scheme) [X.Over S] [Y.Over S], Prop)

/- Lemma 29.49.12 (1): irreducible schemes are birational if and only if they have isomorphic
nonempty open subschemes. -/
@[stacks 0BAA] #check
  (AlgebraicGeometry.Scheme.birational_iff_hasIsomorphicNonemptyOpenSubschemes :
    ∀ (X Y : AlgebraicGeometry.Scheme) [IrreducibleSpace X] [IrreducibleSpace Y],
      AlgebraicGeometry.Scheme.Birational X Y ↔
        AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemes X Y)

/- Lemma 29.49.12 (2): irreducible schemes over `S` are birational over `S` if and only if they
have nonempty open subschemes that are isomorphic over `S`. -/
@[stacks 0BAA] #check
  (AlgebraicGeometry.Scheme.birationalOver_iff_hasIsomorphicNonemptyOpenSubschemesOver :
    ∀ (S X Y : AlgebraicGeometry.Scheme) [X.Over S] [Y.Over S]
      [IrreducibleSpace X] [IrreducibleSpace Y],
      AlgebraicGeometry.Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
        AlgebraicGeometry.HasIsomorphicNonemptyOpenSubschemesOver S X Y)
