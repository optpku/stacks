module

public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Basic
public import StacksCheckRecall.CommandCrossRef

/-!
# Definition 7.43.2

The reusable site-presentation API for subtopoi is owned by ReasLib.  This
Chapter 7 file retains the source label and the direct recall surface.
-/

@[expose] public section

/- Definition 7.43.2 (08LV): a subtopos of `Sh(C)` is the essential image of
the direct image of an embedding of a site-presented topos. -/
@[stacks 08LV] #check @CategoryTheory.GrothendieckTopology.SubtoposPresentation

@[stacks 08LV] #check @CategoryTheory.GrothendieckTopology.IsSubtopos

@[stacks 08LV] #check @CategoryTheory.MorphismOfTopoiIn.isSubtopos_essImage

@[stacks 08LV] #check @CategoryTheory.GrothendieckTopology.IsSubtopos.isClosedUnderIsomorphisms

@[stacks 08LV] #check @CategoryTheory.GrothendieckTopology.isSubtopos_top
