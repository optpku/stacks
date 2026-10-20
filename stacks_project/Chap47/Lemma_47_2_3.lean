/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap47.Definition_47_2_1_Essential
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.Essential
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 47.2.3: A compatible family of essential injections from a fixed module into a
filtered diagram of modules induces an essential injection into the apex of any colimit cocone. -/
@[stacks 08XL] #check
  (CategoryTheory.Subobject.IsEssential.filteredColimit :
    ∀ {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
      (M : ModuleCat.{max v u, u} R) (F : J ⥤ Under M) (c : Cocone F)
      (hc : IsColimit ((Under.forget M).mapCocone c))
      [stageMono : ∀ j, Mono (F.obj j).hom]
      (stageEssential : ∀ j, (imageSubobject (F.obj j).hom).IsEssential),
      Mono c.pt.hom ∧ (imageSubobject c.pt.hom).IsEssential)
