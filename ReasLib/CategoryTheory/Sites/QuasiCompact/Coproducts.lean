/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.QuasiCompact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts of sheaves over quasi-compact site objects

Quasi-compactness of an object of a site is precisely the finiteness input needed for its
set-valued sections functor to commute with arbitrary coproducts.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe s w v u

namespace CategoryTheory.GrothendieckTopology.QuasiCompactObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {W : C}

/-- Lemma 18.30.3 (1): sections of set-valued sheaves over a quasi-compact site object preserve
arbitrary coproducts. -/
@[stacks 0935 "(1)"]
theorem sheafSections_preservesCoproducts (hW : J.QuasiCompactObject W) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      ((sheafSections J (Type (max u v))).obj (op W)) := sorry

end CategoryTheory.GrothendieckTopology.QuasiCompactObject

namespace CategoryTheory.Coverage.QuasiCompactObject

variable {C : Type u} [Category.{v} C] {K : Coverage C} {W : C}

/-- Lemma 18.30.3 (0935) (1): sections over a quasi-compact object of a chosen-cover site
preserve arbitrary coproducts of set-valued sheaves. -/
@[stacks 0935 "(1)"]
theorem sheafSectionsPreservesCoproducts
    (hW : K.QuasiCompactObject W) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      ((sheafSections K.toGrothendieck (Type s)).obj (op W)) := sorry

end CategoryTheory.Coverage.QuasiCompactObject
