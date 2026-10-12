/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RepresentableSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 80.3.4: if `S` is a scheme, `F` and `G` are functors `(Over S)ᵒᵖ ⥤ Type u`
on `(Sch/S)_fppf`, and `a : F ⟶ G` is representable by algebraic spaces, then
`G` being a sheaf for `Scheme.fppfTopology.over S` implies that `F` is a sheaf. -/
@[stacks 02YR]
#check
  (AlgebraicGeometry.isSheaf_fppfTopology_over_of_relativelyRepresentableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}}
      {F G : (Over S)ᵒᵖ ⥤ Type u}
      (a : F ⟶ G),
      AlgebraicSpace.representableByAlgebraicSpaces a →
        Presheaf.IsSheaf (Scheme.fppfTopology.over S) G →
          Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
