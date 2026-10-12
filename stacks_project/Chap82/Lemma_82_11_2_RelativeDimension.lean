/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree

/-!
# Relative dimension of finite locally free morphisms of algebraic spaces

A finite locally free morphism of algebraic spaces has relative dimension `0`,
matching the scheme-level fact for `IsFiniteLocallyFree`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

/-- A finite locally free morphism of algebraic spaces has relative dimension
`0`. -/
instance instRelativeDimension_zero {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteLocallyFree f] : RelativeDimension f 0 :=
  sorry

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
