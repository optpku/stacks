/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Monomorphism
import StacksCheckRecall

/-!
# Flat monomorphisms of algebraic spaces

A flat monomorphism of algebraic spaces is representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.4.1 (David Rydh): A flat monomorphism of algebraic spaces is
representable by schemes. -/
@[stacks 0B8A] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_flat_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [Mono f], yoneda.relativelyRepresentable f)

/- The fibre product of a flat monomorphism of algebraic spaces with a morphism
from a scheme is a scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.isScheme_pullback_of_flat_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Mono f] {T : Over S} (g : ofOver T ⟶ Y),
    IsScheme (pullback f g))

end AlgebraicGeometry.AlgebraicSpace
