/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.UniversallyCatenary
import StacksCheckRecall

/-!
# Dimension functions along locally finite-type morphisms of algebraic spaces

A dimension function on a decent locally Noetherian universally catenary
algebraic space induces a dimension function on a decent algebraic space
locally of finite type over it.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.32.2: Let `S` be a scheme. Let `B` be a decent locally Noetherian
universally catenary algebraic space over `S`, and let `δ : Points B → ℤ` be a
dimension function. If `X` is a decent algebraic space over `B` whose structure
morphism `f : X ⟶ B` is locally of finite type, then
`(relativeDimensionFunction f) δ`, given by
`x ↦ δ (Points.map f x) + (residueFieldTrdegAt f x : ℤ)`, is a dimension
function on `Points X`. -/
@[stacks 0EDN] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsDimensionFunction_relativeDimensionFunction :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
      (f : X ⟶ B) [IsDecent X] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ],
      IsDimensionFunction
        (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ))
