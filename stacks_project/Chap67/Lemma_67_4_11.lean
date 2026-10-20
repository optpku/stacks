module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.Source
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.4.11 (1): if `X` is separated then `X` is separated over `S`. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSeparated.of_isAbsolutelySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X], IsSeparated X)

/- Lemma 67.4.11 (2): if `X` is locally separated then `X` is locally separated over `S`. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallySeparated.of_isAbsolutelyLocallySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyLocallySeparated X],
      IsLocallySeparated X)

/- Lemma 67.4.11 (3): if `X` is quasi-separated then `X` is quasi-separated over `S`. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsQuasiSeparated_of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X],
      IsQuasiSeparated X)

/- Lemma 67.4.11 (4): if `X` is separated over `S` then `f` is separated. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_isSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsSeparated X], Separated f)

/- Lemma 67.4.11 (5): if `X` is locally separated over `S` then `f` is locally separated. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.of_isLocallySeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallySeparated X],
      LocallySeparated f)

/- Lemma 67.4.11 (6): if `X` is quasi-separated over `S` then `f` is quasi-separated. -/
@[stacks 04ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsQuasiSeparated X],
      QuasiSeparated f)
