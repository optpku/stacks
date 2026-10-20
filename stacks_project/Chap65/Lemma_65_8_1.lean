/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry

/- Lemma 65.8.1: for a scheme `S` and sheaves `F`, `G` on `(Sch/S)_fppf`, the coproduct
inclusion `F ⟶ F ⨿ G` in the category of sheaves is representable by open and closed
immersions. -/
@[stacks 0F15] #check (AlgebraicGeometry.sheafCoprodInl_isOpenAndClosedImmersion :
    {S : Scheme.{u}} → {F G : Sheaf (Scheme.fppfTopology.over S) (Type u)} →
    {c : BinaryCofan F G} → IsColimit c →
    (over ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf c.inl.hom)

end AlgebraicGeometry
