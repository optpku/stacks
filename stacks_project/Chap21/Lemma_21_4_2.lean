/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.GlobalSections
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.4.2

Triviality of a torsor is characterized by the existence of a global section in the generic site
API.  The chapter file recalls the two implications and the resulting equivalence without owning
a second translation construction.
-/

open CategoryTheory.Sheaf.Torsor

/- Lemma 21.4.2 (03AI): a global torsor section yields a trivialization. -/
@[stacks 03AI "torsor triviality from a global section"] #check
  @isTrivial_of_nonempty_globalSections

/- Lemma 21.4.2 (03AI): a trivial torsor has a global section. -/
@[stacks 03AI "global section of a trivial torsor"] #check
  @nonempty_globalSections_of_isTrivial

/- Lemma 21.4.2 (03AI): a torsor is trivial exactly when it has a global section. -/
@[stacks 03AI "torsor triviality criterion"] #check
  @isTrivial_iff_nonempty_globalSections
