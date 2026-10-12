/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import stacks_project.Chap65.Definition_65_6_3_Hom

@[expose] public section

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.coproduct :
  {S : AlgebraicGeometry.Scheme.{u}} → {I : Type v} → [Small.{u} I] →
    (I → AlgebraicGeometry.AlgebraicSpace S) → AlgebraicGeometry.AlgebraicSpace S)
