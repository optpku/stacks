module

public import ReasLib.CategoryTheory.Sites.Topos.Localized.Morphism

import StacksCheckRecall

@[expose] public section

/-! [stacks 04IN (1)]
The localization-square comparison is owned by the localized morphism-of-sites API. -/
@[stacks 04IN "(1)"] #check @CategoryTheory.Functor.Localized.inverseImageOverPullback_of_morphism

/-! [stacks 04IN (2)]
The representable-localization comparison is owned by the same API. -/
@[stacks 04IN "(2)"] #check @CategoryTheory.Functor.Localized.representableInverseImage_of_morphism

/-! [stacks 04IN (3)]
Naturality of the localized inverse image is a reusable base-change comparison. -/
@[stacks 04IN "(3)"] #check @CategoryTheory.Functor.Localized.inverseImageOverMapPullback_of_morphism
