/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NonMcQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.GlobalSections
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Counterexamples
import StacksCheckRecall

/-!
# Regular functions of affine formal algebraic spaces need not have enough sections
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- Remark 87.35.2 (1): there exist affine formal algebraic spaces which are not
McQuillan. -/
@[stacks 0DEK] #check (AlgebraicGeometry.exists_isAffineFormalAlgebraicSpace_not_isMcQuillan :
  ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
    (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
    (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
    (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
    IsAffineFormalAlgebraicSpace X ∧ ¬ IsMcQuillan X)

/- Remark 87.35.2 (2): there are affine formal algebraic spaces whose
regular functions do not separate points. -/
@[stacks 0DEK] #check
  (AlgebraicGeometry.exists_isAffineFormalAlgebraicSpace_regularFunctions_not_separatePoints :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (u+1)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X ∧
            IsField (limitGlobalSections D) ∧
              ∃ i : Λ, Infinite ((𝒮.bigAffineToScheme S).obj (D.obj i)))

end AlgebraicGeometry
