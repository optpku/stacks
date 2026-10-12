/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ExternalTensorComplex
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- 57.13.1.2: Equation 57.13.1.2 displays the descending complex with degree `n` term
   `E n ⊠ F.obj (G n)`. -/
@[stacks 0G0A] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ExternalTensorComplex.ofDifferentials :
    {S X Y : AlgebraicGeometry.Scheme} →
      (a : X ⟶ S) →
      (b : Y ⟶ S) →
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        (CategoryTheory.Limits.pullback a b).toRingedSpace] →
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends
        (CategoryTheory.Limits.pullback a b).toRingedSpace] →
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization
        (CategoryTheory.Limits.pullback a b).toRingedSpace] →
      (F : AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤
        AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) →
      (E G : ℕ → AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect
        (X := X.toRingedSpace)) →
      (d : ∀ n,
        AlgebraicGeometry.Scheme.ModuleDerived.ExternalTensorComplex.term
          a b F E G (n + 1) ⟶
        AlgebraicGeometry.Scheme.ModuleDerived.ExternalTensorComplex.term a b F E G n) →
      (squareZero : ∀ n, d (n + 1) ≫ d n = 0) →
      ChainComplex (AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect
        (X := (CategoryTheory.Limits.pullback a b).toRingedSpace)) ℕ)
