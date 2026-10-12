/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_25_3_Square

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- Lemma 78.25.3: Notation and assumption as in Lemma 78.21.1. If the source square
`R --f.arrow→ R'`, `G.s` down, `H.s` down, `U --f.obj→ U'` is cartesian, then the
`2`-commutative square `𝒮_U --atlas_G→ [U/R]`, `𝒮(f.obj)` down, `[f]` down,
`𝒮_{U'} --atlas_H→ [U'/R']` is a `2`-fibre product of stacks in groupoids on
`(Sch/S)_fppf`. -/
@[stacks 04ZN]
theorem atlasCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H)
    (h_source : IsPullback f.arrow G.s H.s f.obj) :
    (atlasCone f).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
