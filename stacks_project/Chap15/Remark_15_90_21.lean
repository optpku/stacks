/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.OpenCover.Algebraic.Pair
import StacksCheckRecall

/-!
# Remark 15.90.21

@stack 05EV
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v

variable {X : TopCat.{v}} (U T : Opens X) (hcover : U ⊔ T = ⊤)

/- Remark 15.90.21 (05EV): for a differential manifold `X`, the complement `U` of a compact
closed submanifold and a tubular neighborhood `T` form a two-open cover. Specifying a sheaf on
`X` is therefore equivalent to specifying sheaves on `U` and `T` together with their gluing
isomorphism over `U ⊓ T`. The reusable owner records the corresponding type-valued sheaf
equivalence for any pair of opens covering a topological space. -/
@[stacks 05EV "two-open-cover sheaf gluing equivalence"]
#check
  TopCat.Sheaf.OpenCover.Gluing.ofSheafFunctor_pair_isEquivalence
    (C := Type v) (F := 𝟭 (Type v)) U T hcover

/- The underlying two-member family of opens. -/
#check TopologicalSpace.OpenCover.pair U T

/- The cover condition supplied by `U ⊔ T = ⊤`. -/
#check TopologicalSpace.OpenCover.pair_isOpenCover hcover
