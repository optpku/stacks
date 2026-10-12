/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Pointed.Adjunction
import StacksCheckRecall

/-!
# Pointed sheaf sections with support in a closed subset

Convenience import for the kernel semantics, functor, adjunction, and exactness API.
-/

@[expose] public section

/- Tag 01B0: sections supported on a closed subset form a functor on pointed sheaves. -/
@[stacks 01B0 "pointed sections-with-support functor"] #check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.functor

/- Tag 01B0: closed-subset pushforward is left adjoint to pointed sections with support. -/
@[stacks 01B0 "pointed closed-support adjunction"] #check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.adjunction

/- Tag 01B0: closed-subset pushforward of pointed sheaves is exact. -/
@[stacks 01B0 "closed-subset pushforward of pointed sheaves is exact"] #check TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed.pushforwardExact
