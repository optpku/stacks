/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Map
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : CommSq f i i' g)

/- Lemma 76.6.3: A commutative square of algebraic spaces over a scheme,
with horizontal immersions, induces a canonical map of graded conormal algebras.
The underlying algebra comparison commutes with every homogeneous inclusion. -/
@[stacks 09RS] #check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.map_graded sq :
    ∀ n : ℕ, ConormalAlgebra.pullbackDegreeToTotal f i' n ≫
        QcAlgebraUnder.underlyingModuleMap (ConormalAlgebra.map sq) =
      ConormalAlgebra.mapPiece sq n ≫ ConormalAlgebra.degreeToTotal i n)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.map sq :
  ConormalAlgebra.pullback f i' ⟶ ConormalAlgebra.total i)
