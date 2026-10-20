/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimit presentations by sheafified representables

Every set-valued sheaf is generated under colimits by the sheafified
representables of its site. This module exposes that presentation without
committing clients to a chosen category-of-elements model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- Every set-valued sheaf admits a small colimit presentation whose diagram consists of
sheafified representables. -/
theorem existsColimitPresentation (ℱ : Sheaf J (Type (max u v))) :
    ∃ (I : Type (max u v)) (_ : SmallCategory I) (U : I ⥤ C)
      (pres : ColimitPresentation I ℱ),
      pres.diag = U ⋙ J.sheafifiedRepresentableFunctor := sorry

end CategoryTheory.GrothendieckTopology.SheafifiedRepresentable
