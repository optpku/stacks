/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.OpenMap
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open TopCat

noncomputable section

universe u

/- Domain-style sampling for Example 7.21.3:
- primary domain: sheaf functors attached to the inclusion of an open subspace;
- sampled owner API:
  `Topology.IsOpenEmbedding.functor_isContinuous`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`,
  `IsOpenMap.cocontinuousPushforwardIso`,
  `Functor.ContinuousRightAdjoint.pushforwardContinuousIso`;
- source/core/bridge triage:
  `source-facing`: compare the sheaf functors induced by the open-subspace site functor with the
  usual restriction `j⁻¹` and direct image `j_*` for `j : U ↪ X`;
  `core/canonical`: `Topology.IsOpenEmbedding.sheafPullbackIso` for the inverse-image side and the
  Chapter 7 owner
  `Functor.ContinuousRightAdjoint.pushforwardContinuousIso` for the
  direct-image side;
  `bridge/view`: the specialization from the inclusion `Opens.inclusion' U` to those owners, in
  particular the owner-scoped open-map comparison
  `IsOpenMap.cocontinuousPushforwardIso`.

Primitive data are only the open `U` and the opens adjunction
`(Opens.isOpenEmbedding U).functor ⊣ Opens.map (Opens.inclusion' U)`. The inverse-image and
direct-image comparisons are derived owner specializations, so this file should reuse those owners
and the existing owner-scoped open-map specialization directly rather than keep parallel local comparison
isomorphisms.
-/

section

variable {X : TopCat.{u}} (U : Opens X)

/- Companion recall: the continuity of the open-subspace functor is already the canonical owner
`Topology.IsOpenEmbedding.functor_isContinuous`. -/
#check @Topology.IsOpenEmbedding.functor_isContinuous

/- Companion recall: the inverse-image comparison for an open embedding is already the canonical
owner `Topology.IsOpenEmbedding.sheafPullbackIso`. -/
#check @Topology.IsOpenEmbedding.sheafPullbackIso

/- Example 7.21.3, inverse-image side: for the inclusion `j : U ↪ X`, the inverse-image functor
coming from the open-subspace site functor is the inverse of the canonical open-embedding
pullback isomorphism. -/
#check
  ((Opens.isOpenEmbedding U).sheafPullbackIso (Type u)).symm

/- Companion recall: the direct-image comparison for a continuous right adjoint is owned by the
Chapter 7 theorem
`Functor.ContinuousRightAdjoint.pushforwardContinuousIso`. -/
#check @Functor.ContinuousRightAdjoint.pushforwardContinuousIso

/- Companion recall: the owner-scoped open-map specialization already packages the direct-image
comparison in the source-facing form used here. -/
#check @IsOpenMap.cocontinuousPushforwardIso

/- Example 7.21.3, direct-image side: the cocontinuous pushforward attached to the open-subspace
functor agrees with the usual direct image `j_*`. -/
@[stacks 00XP] #check
  (Opens.isOpenEmbedding U).isOpenMap.cocontinuousPushforwardIso

end
