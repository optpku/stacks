/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-!
# Cancellation of separation axioms against postcomposition

For morphisms of algebraic stacks, DM and quasi-DM cancel against arbitrary
postcomposition. Separatedness and quasi-separatedness of a composite yield
the same property of the first factor after assuming the relative 2-diagonal
of the second factor is separated or quasi-separated as a representable
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.DM

/-- If a composite morphism of algebraic stacks is DM, then so is the first
factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [DM (f ≫ g)] : DM f := sorry

end AlgebraicGeometry.AlgebraicStack.DM

namespace AlgebraicGeometry.AlgebraicStack.QuasiDM

/-- If a composite morphism of algebraic stacks is quasi-DM, then so is the
first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiDM (f ≫ g)] : QuasiDM f := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiDM

namespace AlgebraicGeometry.AlgebraicStack.Separated

/-- If a composite morphism of algebraic stacks is separated and the relative
2-diagonal of the second factor is separated as a representable morphism of
algebraic spaces, then the first factor is separated. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Separated (f ≫ g)]
    (h_separated :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} g)) :
    Separated f := sorry

end AlgebraicGeometry.AlgebraicStack.Separated

namespace AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-- If a composite morphism of algebraic stacks is quasi-separated and the
relative 2-diagonal of the second factor is quasi-separated as a representable
morphism of algebraic spaces, then the first factor is quasi-separated. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated (f ≫ g)]
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} g)) :
    QuasiSeparated f := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiSeparated
