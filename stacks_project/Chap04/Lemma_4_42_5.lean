module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.FiberPair
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : Groupoids C} {F : X ⟶ Y}
variable (hFaithful : ∀ U : C,
  (fiberFunctor F U).Faithful)
variable (hPairs : Hom.fiberPairClasses.representable F)

/- Lemma 4.42.5: fiberwise faithfulness and representability of the fiber-pair presheaves imply
relative representability. The textbook phrases the second hypothesis after choosing pullbacks
in `Y`; the choice-independent predicate `fiberPairClasses.representable` instead
quantifies a slice-Yoneda representative of each fiber object, which is the stable formal
interface. -/
@[stacks 02Y9]
#check (relativelyRepresentable.ofFiberwiseFaithful
    hFaithful hPairs :
  relativelyRepresentable F)

end FiberedCategoryOver.Groupoids

end CategoryTheory
