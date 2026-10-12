/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.FinitePresentation
import StacksCheckRecall

universe u

/- Lemma 31.9.2: The Fitting ideal sheaf of a finitely presented module is a
quasi-coherent ideal of finite type. -/
@[stacks 0C3E] #check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf_isFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFinitePresentation] (r : ℕ),
      (AlgebraicGeometry.Scheme.fittingIdealSheaf ℱ r).IsFiniteType)
