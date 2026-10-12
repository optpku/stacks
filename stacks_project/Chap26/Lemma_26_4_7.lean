/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.LocallyRingedSpace

/- Lemma 26.4.7 (1): inverse image along a locally ringed-space morphism preserves local
generation of ideals. -/
@[stacks 01HQ] #check IdealSubobject.pullback_isLocallyGenerated
#check ClosedSubspace.IsAssociated.pullback_isLocallyGenerated

/- Lemma 26.4.7 (2): inverse-image closed subspaces have a unique comparison morphism. -/
@[stacks 01HQ "comparison morphism"]
#check ClosedSubspace.IsAssociated.existsUnique_pullbackLift
#check ClosedSubspace.IsAssociated.pullbackComposite_vanishing
#check ClosedSubspace.IsAssociated.pullbackHom_ext

/- Lemma 26.4.7 (3): the comparison square is a pullback square. -/
@[stacks 01HQ "pullback square"]
#check ClosedSubspace.IsAssociated.isPullback_of_commSq
#check ClosedSubspace.IsAssociated.exists_pullback

end AlgebraicGeometry.LocallyRingedSpace
