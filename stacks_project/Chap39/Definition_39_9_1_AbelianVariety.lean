/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety

universe u

#check (AlgebraicGeometry.AbelianVariety :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G], Prop)
