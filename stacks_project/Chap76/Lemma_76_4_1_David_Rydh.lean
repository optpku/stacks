/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat monomorphisms of algebraic spaces

A flat monomorphism of algebraic spaces is representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.4.1 (David Rydh): A flat monomorphism of algebraic spaces is
representable by schemes. -/
@[stacks 0B8A]
theorem relativelyRepresentable_of_flat_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Mono f] :
    yoneda.relativelyRepresentable f :=
  sorry

/-- The fibre product of a flat monomorphism of algebraic spaces with a morphism
from a scheme is a scheme. -/
theorem isScheme_pullback_of_flat_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Mono f] {T : Over S} (g : ofOver T ⟶ Y) :
    IsScheme (pullback f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
