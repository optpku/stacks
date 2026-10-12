/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
import StacksCheckRecall

universe u v

/- Lemma 34.3.12: the category of sheaves on `S_{Zar}` is equivalent to the category of sheaves
on the underlying topological space of `S`. -/
@[stacks 020X] #check
  (AlgebraicGeometry.Scheme.smallZariskiTypeSheafEquiv :
    (S : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.Sheaf S.smallZariskiTopology (Type v) ≌
        TopCat.Sheaf (Type v) (S.toPresheafedSpace : TopCat))
