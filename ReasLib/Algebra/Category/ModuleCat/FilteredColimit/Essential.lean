/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.Essential

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Subobject.IsEssential

/-- A compatible filtered family of essential monomorphisms from a fixed module induces an
essential monomorphism into the apex of a colimit cocone. -/
@[stacks 08XL]
theorem filteredColimit
    {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
    (M : ModuleCat.{max v u, u} R) (F : J ⥤ Under M) (c : Cocone F)
    (hc : IsColimit ((Under.forget M).mapCocone c))
    [stageMono : ∀ j, Mono (F.obj j).hom]
    (stageEssential : ∀ j, (imageSubobject (F.obj j).hom).IsEssential) :
    Mono c.pt.hom ∧ (imageSubobject c.pt.hom).IsEssential := sorry

end CategoryTheory.Subobject.IsEssential
