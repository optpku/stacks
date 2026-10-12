/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_21_2_IsoComma
public import stacks_project.Chap78.Lemma_78_21_2_Square

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- Lemma 78.21.2: Notation and assumption as in Lemma 78.21.1. Let `(U'', R'', s'', t'', c'')`
be the groupoid in algebraic spaces over `B` constructed above. There is a `2`-commutative square
`[U''/R''] --[g]→ [U/R]`, `[U''/R''] → 𝒮_{U'} → [U'/R']`, `[U/R] --[f]→ [U'/R']` which
identifies `[U''/R'']` with the `2`-fibre product. -/
@[stacks 04Y4, instance]
instance isoCommaCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    (isoCommaCone f).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
