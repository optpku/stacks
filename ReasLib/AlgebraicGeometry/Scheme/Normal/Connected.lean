/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.LocallyNoetherian

/-!
# Connected normal schemes

This file relates integrality and connectedness for normal schemes and records the existence of a
normal affine scheme showing that connectedness need not imply irreducibility without finiteness
hypotheses.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- A normal locally Noetherian scheme is integral if and only if it is connected. -/
theorem isIntegral_iff_connectedSpace_of_isNormal
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : X.isNormal) :
    IsIntegral X ↔ ConnectedSpace X := sorry

end AlgebraicGeometry.IsLocallyNoetherian

namespace AlgebraicGeometry.Scheme

/-- There exists a connected affine normal scheme whose stalks are domains but whose underlying
topological space is not irreducible. -/
theorem exists_isAffine_isNormal_connectedSpace_not_irreducibleSpace :
    ∃ X : Scheme.{u}, IsAffine X ∧ X.isNormal ∧ ConnectedSpace X ∧
      (∀ x : X, IsDomain (X.presheaf.stalk x)) ∧ ¬ IrreducibleSpace X := sorry

end AlgebraicGeometry.Scheme
