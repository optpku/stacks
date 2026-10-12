/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded.GraphFunctor

open CategoryTheory

universe u

#check (@AlgebraicGeometry.Correspondence.Graded.graphFunctor :
  (k : Type u) → [Field k] →
    (AlgebraicGeometry.Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      AlgebraicGeometry.Correspondence.Graded.DegreeZero (k := k))
