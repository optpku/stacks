/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback

/-!
# Pullback restriction recall

The reusable comparison is pullback on descent data along a morphism of
fixed-target families, together with its canonical comparison isomorphism.
-/

@[expose] public section

#check @CategoryTheory.DescentDatum.Pullback.functorOfHom
#check @CategoryTheory.DescentDatum.Pullback.canonicalIsoOfHom
#check @CategoryTheory.DescentDatum.Pullback.isoOfHom
#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
