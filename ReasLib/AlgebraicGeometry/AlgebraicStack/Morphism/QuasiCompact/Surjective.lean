/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Isomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Cancellation of quasi-compactness along a surjection

If the first factor of a composite of morphisms of algebraic stacks is
surjective and the composite is quasi-compact, then the second factor is
quasi-compact. The same holds for a hypotenuse 2-isomorphic to the composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- If the first factor of a composite of morphisms of algebraic stacks is
surjective and the composite is quasi-compact, then the second factor is
quasi-compact. -/
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (q : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ q)] :
    QuasiCompact q :=
  sorry

/-- Quasi-compactness of `q : Y ⟶ Z` follows from surjectivity of `f : X ⟶ Y`
and quasi-compactness of a 2-isomorphic hypotenuse `p ≅ f ≫ q`. -/
theorem of_two_commute {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (α : p ≅ f ≫ q)
    [Surjective f] [QuasiCompact p] : QuasiCompact q :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
