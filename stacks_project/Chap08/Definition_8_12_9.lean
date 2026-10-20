module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Existence
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.12.9 -- Inverse image stack

The canonical owner is `CategoryTheory.StackOver.InverseImage`. Its `sourceChoice` field fixes the
explicit bundled pushforward projection, so neither a localization choice nor the direction of
the site functor can be silently omitted from the data.
-/

namespace CategoryTheory

/- Definition 8.12.9: an inverse-image stack of `X` along `u` is an explicit pushforward source,
a target stack, and a stackification comparison between them. -/
@[stacks 04WJ "inverse-image stack along a site functor"]
#check @StackOver.InverseImage

#check @FiberedCategoryOver.Pushforward.ProjectionChoice
#check @StackOver.inverseImageSource
#check @StackOver.inverseImageSource.total
#check @StackOver.inverseImageSource.p
#check @StackOver.InverseImage.sourceChoice
#check @StackOver.InverseImage.target
#check @StackOver.InverseImage.comparison
#check @StackOver.InverseImage.isStackification
#check @StackOver.InverseImage.source
#check @StackOver.InverseImage.source.total
#check @StackOver.InverseImage.source.p
#check @StackOver.InverseImage.comparisonHom
#check @StackOver.InverseImage.comparisonHom.toCartesianBasedFunctor
#check @StackOver.InverseImage.comparisonHom.isStackification
#check @StackOver.InverseImage.nonempty
#check @StackOver.InverseImage.nonemptyCanonical
#check @StackOver.InverseImage.canonical
#check @StackOver.InverseImage.canonical_spec
#check @StackOver.InverseImage.comparisonUnique
#check @StackOver.InverseImage.existsComparisonEquivalence
#check @StackOver.InverseImage.ComparisonChoice
#check @StackOver.InverseImage.ComparisonChoice.of
#check @StackOver.InverseImage.ComparisonChoice.ofExists
#check @StackOver.InverseImage.ComparisonChoice.nonempty
#check @StackOver.InverseImage.comparisonChoice
#check @StackOver.InverseImage.ComparisonChoice.existsUniqueIso
#check @StackOver.InverseImage.ComparisonChoice.comparisonIso
#check @StackOver.InverseImage.ComparisonChoice.comparisonIso_spec
#check @StackOver.InverseImage.ComparisonChoice.comparisonIso_unique
#check @StackOver.InverseImage.canonical.comparison
#check @StackOver.InverseImage.canonical.comparisonChoice
#check @StackOver.InverseImage.comparisonHomUnique
#check @StackOver.InverseImage.existsComparisonHomEquivalence

/- The source definition assumes a morphism of sites.  The reusable owner keeps this hypothesis
separate from the Type-valued inverse-image data, so generic pushforward consumers can work under
weaker assumptions and the source-specific continuity/flatness gate remains explicit. -/
#check @IsMorphismOfSites
#check @IsMorphismOfSites.toIsContinuous
#check @IsMorphismOfSites.toRepresentablyFlat
#check @isMorphismOfSites_iff
#check @IsMorphismOfSites.iff_coverPreserving
#check @IsMorphismOfSites.coverPreserving
#check @IsMorphismOfSites.of_coverPreserving
#check @IsMorphismOfSites.mk'
#check @IsMorphismOfSites.id
#check @IsMorphismOfSites.comp
#check @IsMorphismOfSites.toMorphismOfTopoiIn

end CategoryTheory
