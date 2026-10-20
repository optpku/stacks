module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback
import stacks_project.Chap65.Definition_65_13_2_Separation
import stacks_project.Chap67.Definition_67_4_2_Separation
import stacks_project.Chap76.Lemma_76_32_2

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable {X X' : AlgebraicSpace S} (pX : X ⟶ B) (f : X' ⟶ X)
  [QuasiSeparated pX] [LocallyOfFiniteType pX]
  [QuasiSeparated (f ≫ pX)] [LocallyOfFiniteType (f ≫ pX)]
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable [isInvertibleObject ((Modules.pullback f).obj L)]

/- Remark 82.22.3: In Situation 82.2.1, a morphism `f : X' ⟶ X` of good
algebraic spaces over `B` pulls a triple `(L, s, i : D ⟶ X)` as in
Definition 82.22.1 back to `L' = (Modules.pullback f).obj L`,
`s' = Modules.sectionsPullback f L s`, and `D' = zeroScheme L' s'`, identified
with the fibre product `X' ×_X D` by `zeroSchemePullbackSquare`. This gives a
cartesian square with `i' = zeroSchemeι L' s'` and
`g = zeroSchemePullbackMap f L s`. The maps `i*` and `(i')*` mean `Hom.gysin` of
the two triples; various compatibilities between them may be asked for, but are
not asserted here. -/
@[stacks 0ER3] #check (AlgebraicGeometry.AlgebraicSpace.zeroSchemePullbackSquare f L s :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s))
      (zeroSchemePullbackMap f L s) f (zeroSchemeι L s))

end AlgebraicGeometry.AlgebraicSpace
