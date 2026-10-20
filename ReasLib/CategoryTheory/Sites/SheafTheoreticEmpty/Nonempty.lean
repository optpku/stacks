module

public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Basic

/-!
# Nonempty sheaf topoi

The sheaf topos of a site is nonempty precisely when some object of the site
is not sheaf-theoretically empty.  This site-intrinsic predicate avoids
carrying a chosen witness in APIs that only use nonemptiness as a property.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- Lemma 18.42.5 (093N), site hypothesis: a topology has a nonempty sheaf
topos when some site object is not sheaf-theoretically empty. -/
@[stacks 093N "nonempty topos"]
def HasNonemptySheafTopos (J : GrothendieckTopology C) : Prop :=
  ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U

/-- Unfolding the site-intrinsic nonempty-topos predicate. -/
theorem hasNonemptySheafTopos_iff (J : GrothendieckTopology C) :
    J.HasNonemptySheafTopos ↔ ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U := sorry

end CategoryTheory.GrothendieckTopology
