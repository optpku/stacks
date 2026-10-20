/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UnramifiedQuotient
public import stacks_project.Chap58.Proposition_58_11_3_UnramifiedExtension
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionFieldExtension
universe u

/- Proposition 58.11.3: the quotient uses the actual function-field geometric point and Galois action.
The generic stalk is canonically identified with its residue field by
functionFieldResidueEquiv and functionFieldResidue_triangle. -/
@[stacks 0BQM]
#check (AlgebraicGeometry.Scheme.genericPointInclusion_eq_restrictUnramified :
  {X : Scheme.{u}} → [IsIntegral X] → (hX : X.isNormal) →
    let M := maximalUnramifiedExtension X hX
    ∃ e : fundamentalGroup (functionFieldGeometricPoint X) ≃* Gal(M/X.functionField),
      e.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
        AlgEquiv.restrictNormalHom M)

#check (AlgebraicGeometry.Scheme.genericPointInclusion_restrictUnramified_unique :
  {X : Scheme.{u}} → [IsIntegral X] → (hX : X.isNormal) →
  Function.Surjective (functionFieldFundamentalMap X) →
  (e e' : fundamentalGroup (functionFieldGeometricPoint X) ≃*
    Gal(maximalUnramifiedExtension X hX/X.functionField)) →
  e.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
    AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX) →
  e'.toMonoidHom.comp (functionFieldGaloisMap X).toMonoidHom =
    AlgEquiv.restrictNormalHom (maximalUnramifiedExtension X hX) → e = e')
