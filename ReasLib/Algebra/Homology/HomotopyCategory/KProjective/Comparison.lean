/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KProjective.Characterization
public import ReasLib.CategoryTheory.DerivedCategory.Acyclic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Projective Objects and the Derived Comparison

This leaf identifies the canonical left orthogonal to acyclic homotopy objects
with the objects on which the homotopy-to-derived localization is fully
faithful on outgoing morphisms.
-/

open CategoryTheory ComplexShape DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyCategory.Acyclic

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Stacks 09R0: a homotopy object is left orthogonal to acyclic objects exactly when the
homotopy-to-derived localization is bijective on all maps out of it. -/
@[stacks 09R0]
theorem Qh_map_bijective_iff_leftOrthogonal
    (P : HomotopyCategory A (up ℤ)) :
    (∀ M : HomotopyCategory A (up ℤ),
      Function.Bijective
        (DerivedCategory.Qh.map :
          (P ⟶ M) → (DerivedCategory.Qh.obj P ⟶ DerivedCategory.Qh.obj M))) ↔
      (HomotopyCategory.subcategoryAcyclic A).leftOrthogonal P := sorry

end CategoryTheory.HomotopyCategory.Acyclic
