/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Slice

/-!
# Open immersions of topoi

This leaf owns the open-immersion condition on a morphism of topoi; its
subtopos presentation is supplied by the slice-presentation API.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Definition 7.43.7 (1): an open immersion is an embedding whose direct
image has open-subtopos essential image. -/
@[stacks 08M0, mk_iff isOpenImmersion_iff_embedding_and_openSubtopos]
class IsOpenImmersion (f : MorphismOfTopoiIn J K) : Prop extends IsEmbedding f where
  /-- The essential image of direct image is an open subtopos. -/
  isOpenSubtopos :
    GrothendieckTopology.IsOpenSubtopos.{u₁, u₂, v₁, v₂, w} f.pushforward.essImage

end CategoryTheory.MorphismOfTopoiIn
