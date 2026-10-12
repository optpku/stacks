/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.2.2 — Isomorphism subpresheaf

The canonical owner is `CategoryTheory.Pseudofunctor.isomSubpresheaf`.
-/

namespace CategoryTheory

/- Definition 8.2.2: `Mor(x, y)` is the canonical morphism presheaf. -/
@[stacks 02ZB "morphism presheaf"]
#check @Pseudofunctor.presheafHom

/- Definition 8.2.2: the isomorphism presheaf `Isom(x, y)` is the subpresheaf of `Mor(x, y)`
whose sections are isomorphisms. -/
@[stacks 02ZB "isomorphism subpresheaf"]
#check @Pseudofunctor.isomSubpresheaf
#check @Pseudofunctor.mem_isomSubpresheaf_iff

end CategoryTheory
