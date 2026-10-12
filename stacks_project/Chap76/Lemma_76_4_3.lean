/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Quasi-compact flat surjective monomorphisms of algebraic spaces

A quasi-compact flat surjective monomorphism of algebraic spaces is an
isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.4.3: A quasi-compact flat surjective monomorphism of algebraic
spaces is an isomorphism. -/
@[stacks 0B8C]
theorem isIso_of_quasiCompact_flat_surjective_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Flat f] [Surjective f] [Mono f] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
