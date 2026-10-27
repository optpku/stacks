/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-! # Finiteness properties of affine morphisms of algebraic stacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (Affine)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiCompact

/-- An affine morphism of algebraic stacks is quasi-compact. -/
instance of_affine {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Affine f] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace QuasiSeparated

/-- An affine morphism of algebraic stacks is quasi-separated. -/
instance of_affine {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Affine f] : QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack
