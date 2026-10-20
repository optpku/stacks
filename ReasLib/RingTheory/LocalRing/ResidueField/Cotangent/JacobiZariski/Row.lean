/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.JacobiZariski
import Mathlib.Tactic.CrossRefAttribute

/-!
# The residue-field Jacobi--Zariski row

@stack 0DYH

This leaf packages the universe-polymorphic residue-field Jacobi--Zariski maps
as a zero-ended row in `ModuleCat`.  The same-universe restriction belongs only
to this categorical facade.
-/

@[expose] public section

open CategoryTheory
open Algebra
open IsLocalRing
open KaehlerDifferential
open scoped TensorProduct ZeroObject

universe u

namespace Algebra.H1Cotangent.ResidueField

noncomputable section

variable {A B : Type u}
variable [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]
variable (A B)

/-- The complete zero-ended residue-field Jacobi--Zariski row. -/
@[stacks 0DYH "residue-field Jacobi--Zariski row"]
noncomputable def row :
    ComposableArrows (ModuleCat (ResidueField B)) 5 :=
  ComposableArrows.mk₅
    (0 : (0 : ModuleCat (ResidueField B)) ⟶
      ModuleCat.of (ResidueField B) (H1Cotangent A (ResidueField B)))
    (ModuleCat.ofHom (toCotangent A B))
    (ModuleCat.ofHom (IsLocalRing.ResidueField.conormal (A := A) (B := B)))
    (ModuleCat.ofHom (mapBaseChange A B (ResidueField B)))
    (0 : ModuleCat.of (ResidueField B) Ω[ResidueField B⁄A] ⟶
      (0 : ModuleCat (ResidueField B)))

/-- The packaged residue-field row is exact precisely when its first nonzero arrow is injective.
The other exactness points are supplied by `toCotangent_exact`,
`IsLocalRing.ResidueField.conormal_exact`, and
`IsLocalRing.ResidueField.mapBaseChange_surjective`. -/
@[simp, stacks 0DYH "residue-field row exactness criterion"]
theorem row_exact_iff :
    (row A B).Exact ↔ Function.Injective (toCotangent A B) := sorry

end

end Algebra.H1Cotangent.ResidueField
