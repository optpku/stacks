/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits and right lifting properties

A right lifting property is stable under a colimit when each testing arrow is compact for that
particular arrow diagram.  The fixed-diagram theorem is the primitive interface; shape-wide and
filtered-colimit theorems package the same condition at successively more uniform levels.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe w w' v u

namespace CategoryTheory.MorphismProperty.rlp

variable {C : Type u} [Category.{v} C]

/-- The colimit arrow of a diagram of maps in `I.rlp` again lies in `I.rlp` when every test
arrow in `I` is compact for this particular arrow diagram. -/
@[stacks 08Q5 "arrow-colimit elimination for right lifting properties"]
theorem arrowColimit (I : MorphismProperty C) {J : Type w'} [Category.{w} J]
    (F : J ⥤ Arrow C) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, I.rlp (F.obj j).hom)
    (hI : ∀ i : I.toSet,
      PreservesColimit F (coyoneda.obj (Opposite.op i.1))) :
    I.rlp c.pt.hom := sorry

/-- Right lifting against `I` is stable under colimits of shape `J` when every test arrow in
`I`, regarded as an object of `Arrow C`, has a covariant Hom functor preserving `J`-colimits.
No filteredness assumption on `J` is needed at this level. -/
@[stacks 08Q5 "shape-wide colimit stability of right lifting properties"]
theorem colimitsOfShape (I : MorphismProperty C)
    (J : Type w') [Category.{w} J]
    (hI : ∀ i : I.toSet,
      PreservesColimitsOfShape J (coyoneda.obj (Opposite.op i.1))) :
    I.rlp.IsStableUnderColimitsOfShape J := sorry

/-- Right lifting against `I` is stable under filtered colimits when every arrow in `I`, regarded
as an object of `Arrow C`, is compact for filtered colimits of the prescribed universe sizes. -/
@[stacks 08Q5 "filtered-colimit stability of right lifting properties"]
theorem filteredColimits (I : MorphismProperty C)
    (hI : ∀ i : I.toSet,
      PreservesFilteredColimitsOfSize.{w, w'}
        (coyoneda.obj (Opposite.op i.1))) :
    I.rlp.IsStableUnderFilteredColimits.{w, w'} := sorry

end CategoryTheory.MorphismProperty.rlp
