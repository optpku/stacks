/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.MorphismProperty.Over

/-!
# Separatedness of product maps in a slice
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {A B C D : Over S}

/-- Lemma 26.21.12 (5): a binary product map over `S` is separated when both components are. -/
@[stacks 01KU]
instance isSeparated_overProdMap
    (f : A ⟶ B) (g : C ⟶ D) [IsSeparated f.left] [IsSeparated g.left] :
    IsSeparated (prod.map f g).left := sorry

/-- Lemma 26.21.12 (6): a binary product map over `S` is quasi-separated when both components
are. -/
@[stacks 01KU]
instance quasiSeparated_overProdMap
    (f : A ⟶ B) (g : C ⟶ D) [QuasiSeparated f.left] [QuasiSeparated g.left] :
    QuasiSeparated (prod.map f g).left := sorry

end AlgebraicGeometry
