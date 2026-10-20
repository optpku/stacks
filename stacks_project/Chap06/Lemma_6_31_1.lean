/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Opens.SectionComparison
public import ReasLib.Topology.Sheaves.Stalks.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 6.31.1 (1): pullback of a presheaf along an open inclusion evaluates on an open subset
by evaluating the original presheaf on its ambient image. -/
@[stacks 00A0 "presheaf restriction along an open inclusion"]
recall TopCat.Presheaf.pullbackObjObjOfImageOpen

/- Lemma 6.31.1 (2): pullback of a sheaf along an open inclusion is canonically isomorphic to
the naive restriction obtained by composition with the image-of-opens functor. -/
@[stacks 00A0 "sheaf restriction along an open inclusion"]
recall Topology.IsOpenEmbedding.sheafPullbackIso

/- Lemma 6.31.1 (3): pullback identifies the stalk at a point of the open subspace with the
stalk of the original sheaf at its image in the ambient space. -/
@[stacks 00A0 "stalk identification under open restriction"]
recall TopCat.Sheaf.stalkPullbackIso

/- Lemma 6.31.1 (4): on presheaves over an open subset, the counit `j_p j_* ⟶ 𝟭` of pullback
followed by pushforward is an isomorphism. -/
@[stacks 00A0 "presheaf pullback-pushforward counit"]
recall TopCat.Opens.Subspace.presheafPullbackPushforwardCounit_isIso

/- Lemma 6.31.1 (5): on sheaves over an open subset, the counit `j⁻¹ j_* ⟶ 𝟭` of pullback
followed by pushforward is an isomorphism. -/
@[stacks 00A0 "sheaf pullback-pushforward counit"]
recall TopCat.Opens.Subspace.sheafPullbackPushforwardCounit_isIso
