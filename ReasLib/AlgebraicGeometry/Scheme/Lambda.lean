/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.SetTheory.Cardinal.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Size

/-!
# Residue-field cardinal bound of a scheme

The invariant `lambda` is the smallest infinite cardinal bounding all residue-field
cardinalities of a scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.Scheme

/-- The smallest infinite cardinal bounding the cardinalities of residue fields of
a scheme. -/
noncomputable def lambda (T : Scheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ ⨆ t : T, #(T.residueField t)

/-- `lambda T` is the supremum of `ℵ₀` and the cardinalities of the residue fields
of `T`. -/
theorem lambda_def (T : Scheme.{u}) :
    lambda T = ℵ₀ ⊔ ⨆ t : T, #(T.residueField t) :=
  sorry

/-- Countable infinite cardinals are bounded by `lambda T`. -/
theorem aleph0_le_lambda (T : Scheme.{u}) : ℵ₀ ≤ lambda T := sorry

/-- The cardinality of a residue field is bounded by `lambda T`. -/
theorem cardinalMk_residueField_le_lambda (T : Scheme.{u}) (t : T) :
    #(T.residueField t) ≤ lambda T :=
  sorry

/-- `lambda T` is bounded by the Stacks size of `T`. -/
theorem lambda_le_size (T : Scheme.{u}) : lambda T ≤ T.size := sorry

end AlgebraicGeometry.Scheme
