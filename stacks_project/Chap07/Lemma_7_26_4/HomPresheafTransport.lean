/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.BaseChange
public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Computations

/-!
# Hom-presheaf transport recall

The reusable owner for the former coercion-heavy normal forms is the canonical
Hom-presheaf base-change API together with `pullHom` composition calculations.
-/

@[expose] public section

#check @CategoryTheory.Pseudofunctor.PresheafHom.BaseChange.Hom.app
#check @CategoryTheory.Pseudofunctor.PresheafHom.BaseChange.Inv.app
#check @CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map_comp
