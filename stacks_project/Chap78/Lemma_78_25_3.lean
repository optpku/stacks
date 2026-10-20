module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasNaturality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/- Lemma 78.25.3: Notation and assumption as in Lemma 78.21.1. If the source square
`R --f.arrow→ R'`, `G.s` down, `H.s` down, `U --f.obj→ U'` is cartesian, then the
`2`-commutative square `𝒮_U --atlas_G→ [U/R]`, `𝒮(f.obj)` down, `[f]` down,
`𝒮_{U'} --atlas_H→ [U'/R']` is a `2`-fibre product of stacks in groupoids on
`(Sch/S)_fppf`. -/
@[stacks 04ZN] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.atlasCone_isBilimit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
      (f : Hom G H), IsPullback f.arrow G.s H.s f.obj → (atlasCone f).IsBilimit)

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
