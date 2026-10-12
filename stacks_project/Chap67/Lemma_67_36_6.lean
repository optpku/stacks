/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Syntomic morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Syntomic

/-- Lemma 67.36.6: A syntomic morphism is flat. -/
@[stacks 0DEZ]
instance flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Syntomic f] : Flat f :=
  sorry

end Syntomic

end AlgebraicGeometry.AlgebraicSpace
