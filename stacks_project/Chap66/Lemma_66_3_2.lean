/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.3.2 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`. Among the
absolute separation axioms of Definition 66.3.1, absolute separatedness of `X` implies
absolute local separatedness and absolute quasi-separatedness, and hence (with (2)) all of
the others. -/
@[stacks 03DY] #check
  (instIsAbsolutelyLocallySeparated_of_isAbsolutelySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X],
      IsAbsolutelyLocallySeparated X)

@[stacks 03DY] #check
  (instIsAbsolutelyQuasiSeparated_of_isAbsolutelySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X],
      IsAbsolutelyQuasiSeparated X)

/- Lemma 66.3.2 (2): let `S` be a scheme. Let `X` be an algebraic space over `S`. Absolute
quasi-separatedness of `X` implies that `X` is absolutely Zariski locally quasi-separated. -/
@[stacks 03DY] #check
  (instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X],
      IsAbsolutelyZariskiLocallyQuasiSeparated X)
