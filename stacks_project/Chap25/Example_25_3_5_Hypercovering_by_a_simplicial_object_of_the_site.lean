module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
import StacksCheckRecall

/-!
# Hypercoverings by simplicial objects of a site

The reusable construction is owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Augmented`.
-/

open CategoryTheory

/- Example 25.3.5 (Hypercovering by a simplicial object of the site): the singleton-family lift
of an augmented simplicial object is a hypercovering precisely when its augmentation and relative
matching maps are covering arrows. -/
@[stacks 0GM9] #check @SimplicialObject.Augmented.toOverFamily_isHypercovering_iff

-- The corresponding reusable data constructor.
#check @SimplicialObject.Augmented.toHypercovering

-- The source-facing degree-zero, degree-one, and higher matching-map consequences.
#check @SimplicialObject.Augmented.IsHypercovering.zero
#check @SimplicialObject.Augmented.IsHypercovering.one
#check @SimplicialObject.Augmented.IsHypercovering.higher
