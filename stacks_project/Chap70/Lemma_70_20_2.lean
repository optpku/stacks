/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.FinitePresentation
import StacksCheckRecall

/-!
# Testing universal closedness of quasi-compact morphisms of algebraic spaces

Universal closedness can be tested by locally finitely presented base changes
or by affine-space products after a surjective étale scheme atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.20.2: universal closedness, locally finitely presented base-change
closedness, and closed affine-space tests on a surjective étale scheme atlas
are equivalent for a quasi-compact morphism of algebraic spaces. -/
@[stacks 0CM9] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.tfae_quasiCompact :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f],
    List.TFAE [UniversallyClosed f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f])

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_forallLocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f],
    UniversallyClosed f ↔ Closed.forallLocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existsEtaleAffineSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f],
    UniversallyClosed f ↔ Closed.existsEtaleAffineSpace f)

end AlgebraicGeometry.AlgebraicSpace
