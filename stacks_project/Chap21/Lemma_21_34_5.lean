module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.5

The iterated internal-Hom comparison is the generic source-order construction.  Its specification
and uncurried form are exposed directly so later refinements can use the map rather than an
existential isomorphism view.
-/

/- Lemma 21.34.5 (0A92): iterated internal-Hom comparison. -/
@[stacks 0A92 "iterated internal-Hom comparison"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map

@[stacks 0A92 "iterated internal-Hom comparison specification"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map_spec
@[stacks 0A92 "iterated internal-Hom comparison uncurried form"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map_uncurry
