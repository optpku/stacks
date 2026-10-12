/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.9.1 (02ZP) (1): each Hom-presheaf comparison presents its target as a
sheafification, including both membership in the localizing class and target sheafness. -/
@[stacks 02ZP "(1) Hom-presheaf sheafification condition"]
#check @CartesianBasedFunctor.IsStackification.homSheafification

#check @Presheaf.IsSheafification.mem_W
#check @Presheaf.IsSheafification.isSheaf
#check @CartesianBasedFunctor.IsLocalEquivalence.homPresheafMap_mem

@[stacks 02ZP "(2) local essential-surjectivity condition"]
#check @CartesianBasedFunctor.LocallyEssentiallySurjective.iff_forall_cover

@[stacks 02ZP "existence of stackification in groupoids"]
#check @Functor.IsFibered.InGroupoids.Stackification.existsOverSite
#check @Functor.IsFibered.InGroupoids.Stackification.Presentation
#check @Functor.IsFibered.InGroupoids.Stackification.Presentation.of
#check @Functor.IsFibered.InGroupoids.Stackification.Presentation.ofExists
#check @Functor.IsFibered.InGroupoids.Stackification.Presentation.nonempty
#check @Functor.IsFibered.InGroupoids.Stackification.presentation
#check @Functor.IsFibered.InGroupoids.Stackification.Presentation.toPresentation

/- The unnumbered uniqueness clause is owned by the heterogeneous theorem, which directly
accepts the enlarged-universe comparisons returned by `existsOverSite`. -/
@[stacks 02ZP "uniqueness of stackification in groupoids"]
#check @CartesianBasedFunctor.IsStackification.comparisonUnique

#check @CartesianBasedFunctor.IsStackification
#check @CartesianBasedFunctor.IsStackification.iff_isLocalEquivalence_and_isStack

/- The fixed-universe bundled theorem remains a convenient groupoid-stack specialization. -/
#check @StackOver.Groupoids.Stackification.comparisonUnique

end CategoryTheory
