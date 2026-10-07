module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCheckRecall

@[expose] public section

open CategoryTheory GrothendieckTopology

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) (E : Type w)

/- Definition 7.32.6: let p be a point of the site C given by the functor u.
For a set E we define p_* E = u^s E, the sheaf described in Lemma 7.32.5.
We sometimes call this a skyscraper sheaf.

The canonical owner is `Point.skyscraperSheafFunctor` specialized to sets
`Type w`, with value `Φ.skyscraperSheaf E`. -/
@[stacks 00Y9] #check (Φ.skyscraperSheafFunctor : Type w ⥤ Sheaf J (Type w))

#check (Φ.skyscraperSheaf E : Sheaf J (Type w))
