/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra
import StacksCheckRecall

universe u

/- 97.13.0.2: `FA d` is the functor `Sch_fppfᵒᵖ ⥤ Groupoids` sending a scheme `T`
to the groupoid of free `d`-dimensional algebras over `Γ(T, ⊤)`. The fppf
decoration is the ambient site `Scheme.fppfTopology`, not a restriction of
objects. -/
@[stacks 05YN] #check
  (@AlgebraicGeometry.FA : ∀ (d : ℕ) [NeZero d],
    CategoryTheory.Functor (AlgebraicGeometry.Scheme.{u})ᵒᵖ
      CategoryTheory.Grpd.{u, u})
