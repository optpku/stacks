/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.42.2

The generic equivalent characterizations of sheaf-theoretically empty objects
are owned by ReasLib.
-/

@[expose] public section

/- Lemma 7.42.2 (04B6): sheaf theoretical emptiness, unique sections,
nonempty sections of the sheafified initial presheaf, and a covering bottom
sieve are equivalent. -/
@[stacks 04B6] #check @CategoryTheory.GrothendieckTopology.isSheafTheoreticallyEmpty_tfae
#check @CategoryTheory.GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem
#check @CategoryTheory.GrothendieckTopology.isSheafTheoreticallyEmpty_iff_sheafifyInitial_nonempty
#check @CategoryTheory.GrothendieckTopology.isSheafTheoreticallyEmpty_iff_sheafifyInitial_unique
#check @CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty.of_arrow
