module

public import ReasLib.CategoryTheory.Sites.Topos.Immersion
public import StacksCheckRecall.CommandCrossRef

/-!
# Definition 7.43.7

Open and closed immersion assumptions are reusable properties of morphisms of
topoi, so their owner is the ReasLib topos layer rather than Chapter 7.
-/

@[expose] public section

/- Definition 7.43.7 (08M0) (1): an open immersion is an embedding with open
essential image. -/
@[stacks 08M0 "(1)"] #check @CategoryTheory.MorphismOfTopoiIn.IsOpenImmersion

/- Definition 7.43.7 (08M0) (2): a closed immersion is an embedding with
closed essential image. -/
@[stacks 08M0 "(2)"] #check @CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion
