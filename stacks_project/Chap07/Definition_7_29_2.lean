module

public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import StacksCheckRecall

@[expose] public section

/- Definition 7.29.2: for sites C and D, a special cocontinuous functor u : C ⥤ D is a
cocontinuous functor of sites satisfying the five comparison conditions of Lemma 7.29.1
(continuous, cocontinuous, source-locally faithful, source-locally full, and cover-dense).
This is the unbundled Prop class Functor.IsSpecialCocontinuous J K; the induced
equivalence of topoi is the comparison theorem, not a definition field. -/
@[stacks 03CG] #check (@CategoryTheory.Functor.IsSpecialCocontinuous :
  {C : Type _} → [CategoryTheory.Category C] → {D : Type _} →
    [CategoryTheory.Category D] → CategoryTheory.Functor C D →
      CategoryTheory.GrothendieckTopology C →
        CategoryTheory.GrothendieckTopology D → Prop)

#check @CategoryTheory.Functor.isSpecialCocontinuous_iff
