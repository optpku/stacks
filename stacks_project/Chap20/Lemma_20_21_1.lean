module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

/- Lemma 20.21.1 (0A3A): sections supported on a closed subset of an injective abelian sheaf
form an injective abelian sheaf on that subset. -/
@[stacks 0A3A]
#check fun {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℐ : X.Sheaf AddCommGrpCat.{u}) (hℐ : Injective ℐ) ↦
  (TopCat.Sheaf.ClosedSubset.SectionsWithSupport.injectiveObj hZ ℐ hℐ :
    Injective
      ((TopCat.Sheaf.ClosedSubset.SectionsWithSupport.functor
        (C := AddCommGrpCat.{u}) hZ).obj ℐ))
