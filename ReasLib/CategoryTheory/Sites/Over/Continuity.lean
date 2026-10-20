/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Continuity on slice sites

This leaf records the canonical continuity consequences of passage to a slice
site.  It is separate from flatness and morphisms of sites so it remains useful
for an arbitrary continuous functor.
-/

@[expose] public section

universe uC vC uD vD w

namespace CategoryTheory

/-- A continuous functor remains continuous after passing to the slice sites
over an object and its image.  All inputs are determined by the target
slice-site functor, so this canonical fact is available to typeclass search. -/
@[stacks 03CF]
instance Functor.IsContinuous.overPost
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] (U : C) :
    (Over.post u).IsContinuous (J.over U) (K.over (u.obj U)) := sorry

/-- Composing the canonical slice forgetful functor with a continuous functor is continuous.
Unlike general composition, the intermediate topology `J` is determined by the source
`J.over U`, so this specialization is safe for typeclass search. -/
@[stacks 03CF "slice forget composite"]
instance Functor.IsContinuous.overForgetComp
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (u : C ⥤ D) {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} [u.IsContinuous J K] (U : C) :
    (Over.forget U ⋙ u).IsContinuous (J.over U) K := sorry

/-- Precomposition along `Over.post u` preserves the sheaf condition when
`u` is continuous. -/
theorem Functor.IsContinuous.overPost_op_comp_isSheaf
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (u : C ⥤ D) {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [u.IsContinuous J K] {U : C}
    (P : (Over (u.obj U))ᵒᵖ ⥤ Type w)
    (hP : Presheaf.IsSheaf (K.over (u.obj U)) P) :
    Presheaf.IsSheaf (J.over U) ((Over.post u).op ⋙ P) := sorry

end CategoryTheory
