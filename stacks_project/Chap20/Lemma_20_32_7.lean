/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying
open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison

/-
Lemma 20.32.7 (0D5Y): for a derived module `K`, derived sections on an open set agree with
derived sections of the underlying abelian sheaf; for a morphism of ringed spaces, derived
pushforward commutes with passage to underlying abelian sheaves.  The reusable owners expose both
the functor-level isomorphisms and their objectwise components.
-/

@[stacks 0D5Y "Lemma 20.32.7 (1): derived sections and underlying abelian sheaves"]
#check @isomorphic

@[stacks 0D5Y "Lemma 20.32.7 (2): derived pushforward and underlying abelian sheaves"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.comparisonIso

@[stacks 0D5Y "derived sections and underlying abelian sections"]
#check @AlgebraicGeometry.RingedSpace.moduleDerivedSectionsAtOpenToAb_isomorphic_moduleSectionsAsAbelianDerived
@[stacks 0D5Y "underlying sections comparison source"]
#check @canonicalSource
@[stacks 0D5Y "underlying sections comparison target"]
#check @canonicalTarget
@[stacks 0D5Y "underlying sections comparison isomorphism"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison.comparisonIso
@[stacks 0D5Y "underlying sections comparison component"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.UnderlyingComparison.appIso
@[stacks 0D5Y "underlying pushforward functor"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.functor
@[stacks 0D5Y "underlying derived pushforward functor"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.derivedFunctor
@[stacks 0D5Y "underlying pushforward comparison source"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.source
@[stacks 0D5Y "underlying pushforward comparison target"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.target
@[stacks 0D5Y "underlying pushforward comparison component"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Underlying.appIso

end
