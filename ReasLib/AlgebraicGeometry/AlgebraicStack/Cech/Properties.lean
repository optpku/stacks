/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Simplex

/-! # Algebraicity and finiteness of Čech projections of algebraic stacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- Every covering simplex of a morphism of algebraic stacks is an algebraic stack. -/
instance cechCovering [AlgebraicStack U] [AlgebraicStack X]
    (f : U ⟶ X) (n : SimplexCategory) :
    AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f n) := sorry

/-- The Čech projections of a quasi-compact morphism are quasi-compact. -/
instance cechProj_quasiCompact [AlgebraicStack U] [AlgebraicStack X]
    (f : U ⟶ X) [QuasiCompact f] (n : SimplexCategory) :
    QuasiCompact (Cech.proj.{u + 1, u, u + 1, u} f n) := sorry

/-- The Čech projections of a quasi-separated morphism are quasi-separated. -/
instance cechProj_quasiSeparated [AlgebraicStack U] [AlgebraicStack X]
    (f : U ⟶ X) [QuasiSeparated f] (n : SimplexCategory) :
    QuasiSeparated (Cech.proj.{u + 1, u, u + 1, u} f n) := sorry

/-- Composing a Čech projection of a quasi-separated morphism with a
quasi-separated morphism gives a quasi-separated morphism. -/
instance cechProjComp_quasiSeparated
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y) [QuasiSeparated f] [QuasiSeparated g]
    (n : SimplexCategory) :
    QuasiSeparated (Cech.proj.{u + 1, u, u + 1, u} f n ≫ g) := sorry

end AlgebraicGeometry.AlgebraicStack
