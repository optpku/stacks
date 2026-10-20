/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Countable.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicTypes

/-!
# Countable presentations of affine formal algebraic spaces

An affine formal algebraic space admits a sequential affine-thickening
presentation exactly when it admits a countable directed affine-thickening
presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- An affine formal algebraic space has a sequential affine-thickening
presentation if and only if it has a countable directed affine-thickening
presentation. -/
theorem exists_natDirectedAffineThickeningColimit_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (∃ D : ℕ ⥤ 𝒮.bigAffineSite S, IsNatDirectedAffineThickeningColimit D X) ↔
      (∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (_ : Countable Λ) (D : Λ ⥤ 𝒮.bigAffineSite S),
        IsDirectedAffineThickeningColimit D X) := sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
