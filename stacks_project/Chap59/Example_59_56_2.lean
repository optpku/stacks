/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_56_1_ResidueGalois
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
import StacksCheckRecall

open AlgebraicGeometry

@[expose] public section

noncomputable section

/-- Example 59.56.2: The geometric point from `Spec ℂ ⟶ Spec ℚ` induced by
the canonical map is not algebraic. -/
@[stacks 03QY]
theorem complexGeometricPoint_not_isAlgebraic :
    ¬ (Scheme.GeometricPoint.of ℂ
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))).IsAlgebraic := sorry
