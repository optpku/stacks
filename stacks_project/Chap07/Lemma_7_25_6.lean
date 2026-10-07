module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.LowerShriek
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.6 (0E8E): localization lower shriek reflects monomorphisms and epimorphisms. -/
@[stacks 0E8E "(1)"] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.reflectsMonomorphisms

@[stacks 0E8E "(2)"] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.reflectsEpimorphisms
