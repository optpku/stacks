module

public import stacks_project.Chap67.Definition_67_4_2_Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.4.3 (1): if `f` is separated then `f` is locally separated. -/
@[stacks 03KK] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallySeparated.of_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
      LocallySeparated f)

/- Lemma 67.4.3 (2): if `f` is separated then `f` is quasi-separated. -/
@[stacks 03KK] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
      QuasiSeparated f)
