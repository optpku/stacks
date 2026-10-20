/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.GlobalSections

/-!
# Affine formal algebraic spaces with few global functions
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- There exists an affine formal algebraic space admitting a directed affine
thickening presentation with field-valued inverse-limit global sections and an
infinite affine stage. -/
theorem exists_isAffineFormalAlgebraicSpace_regularFunctions_not_separatePoints :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (u+1)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X ∧
            IsField (limitGlobalSections D) ∧
              ∃ i : Λ, Infinite ((𝒮.bigAffineToScheme S).obj (D.obj i)) := sorry

end AlgebraicGeometry
