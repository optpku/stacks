/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Smooth morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Smooth

/-- Lemma 67.37.7: A smooth morphism of algebraic spaces is flat. -/
@[stacks 04TA]
instance flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : Flat f :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace
