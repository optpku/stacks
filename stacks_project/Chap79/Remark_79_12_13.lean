/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.FinitePart
import StacksCheckRecall

/-!
# A finite origin morphism whose finite-part sheaf is not a scheme

The finite morphism `Spec(ℂ) ⟶ A¹_ℝ` at the real rational origin has a finite-part
sheaf isomorphic to the quadratic Galois quotient associated to `ℝ ⊂ ℂ`.
This sheaf is not representable by a scheme.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/- Remark 79.12.13: The finite-part sheaf of the complex origin over the real affine
line is not a scheme, although the origin morphism is finite. -/
@[stacks 04QJ] #check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_isRepresentable_originFinitePart :
    ¬ ∃ T : Over (base ℝ),
        Nonempty
          (originFinitePart ≅
            (Scheme.fppfTopology.over (base ℝ)).uliftYoneda.{1}.obj T))

#check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.instIsFinite_originOver_realComplex :
    AlgebraicGeometry.IsFinite (originOver ℝ ℂ).hom)

#check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.originFinitePart_iso_sheafOfPoints :
    Nonempty (originFinitePart ≅ sheafOfPoints ℝ ℂ Complex.finrank_real_complex))
