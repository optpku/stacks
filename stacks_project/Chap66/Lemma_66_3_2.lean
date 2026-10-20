module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.3.2 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`. Among the
absolute separation axioms of Definition 66.3.1, absolute separatedness of `X` implies
absolute local separatedness and absolute quasi-separatedness, and hence (with (2)) all of
the others. -/
@[stacks 03DY] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyLocallySeparated_of_isAbsolutelySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X],
      IsAbsolutelyLocallySeparated X)

@[stacks 03DY] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyQuasiSeparated_of_isAbsolutelySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X],
      IsAbsolutelyQuasiSeparated X)

/- Lemma 66.3.2 (2): let `S` be a scheme. Let `X` be an algebraic space over `S`. Absolute
quasi-separatedness of `X` implies that `X` is absolutely Zariski locally quasi-separated. -/
@[stacks 03DY] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X],
      IsAbsolutelyZariskiLocallyQuasiSeparated X)
