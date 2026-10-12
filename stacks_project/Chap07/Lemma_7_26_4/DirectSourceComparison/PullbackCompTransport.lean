/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Computations

/-!
# Pullback-composition transport recall

The comparison between two pullback presentations is the canonical family
pullback isomorphism, while component transport is covered by `pullHom`.
-/

@[expose] public section

#check @CategoryTheory.DescentDatum.Pullback.canonicalIso
#check @CategoryTheory.DescentDatum.Pullback.iso
#check @CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp₃
