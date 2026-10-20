module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
import StacksCheckRecall

/-!
# Transfer of separation axioms along morphisms of algebraic spaces

If a morphism of algebraic spaces is separated, locally separated, or
quasi-separated, then the corresponding absolute and relative separation
axioms pass from the target to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.4.9 (1): if `Y` is separated and `f : X ⟶ Y` is separated, then `X` is
separated. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated.of_separated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAbsolutelySeparated Y] [Separated f], IsAbsolutelySeparated X)

/- Lemma 67.4.9 (2): if `Y` is quasi-separated and `f : X ⟶ Y` is quasi-separated, then
`X` is quasi-separated. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.of_quasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAbsolutelyQuasiSeparated Y] [QuasiSeparated f], IsAbsolutelyQuasiSeparated X)

/- Lemma 67.4.9 (3): if `Y` is locally separated and `f : X ⟶ Y` is locally separated,
then `X` is locally separated. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyLocallySeparated.of_locallySeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsAbsolutelyLocallySeparated Y] [LocallySeparated f], IsAbsolutelyLocallySeparated X)

/- Lemma 67.4.9 (4): if `Y` is separated over `S` and `f : X ⟶ Y` is separated, then `X`
is separated over `S`. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsSeparated.of_separated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsSeparated Y] [Separated f], IsSeparated X)

/- Lemma 67.4.9 (5): if `Y` is quasi-separated over `S` and `f : X ⟶ Y` is
quasi-separated, then `X` is quasi-separated over `S`. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated.of_quasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiSeparated Y] [QuasiSeparated f], IsQuasiSeparated X)

/- Lemma 67.4.9 (6): if `Y` is locally separated over `S` and `f : X ⟶ Y` is locally
separated, then `X` is locally separated over `S`. -/
@[stacks 04ZH] #check (AlgebraicGeometry.AlgebraicSpace.IsLocallySeparated.of_locallySeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallySeparated Y] [LocallySeparated f], IsLocallySeparated X)

end AlgebraicGeometry.AlgebraicSpace
