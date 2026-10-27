/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.NoetherianUniversalClosed

/-!
# Local erratum: Noetherian valuative tests for universal closedness

This local erratum was approved on 2026-10-01. It adds quasi-separatedness to
the equivalences and the universally-closed-to-existence direction, while
retaining DVR-extension implying universal closedness without that assumption.
The uploaded source remains unchanged. The corrected reverse implication uses
the quasi-separated criterion (tag 0A3X), not the one-direction criterion 03KA.

A quasi-separated finite-type morphism of algebraic spaces into a locally Noetherian target is
universally closed iff it satisfies the existence part of the valuative
criterion, iff some surjective étale scheme atlas of the target has closed
affine-space product projections, iff every DVR valuative square admits a
finite separable dominating discrete valuation ring extension with a lift, and
iff every DVR valuative square admits some dominating valuation-ring extension
with a lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/- Lemma 70.21.4 (local erratum): for a quasi-separated finite-type morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S` with `Y` locally Noetherian, the following are equivalent:
`UniversallyClosed f`; the existence part of the valuative criterion; the
existence of a scheme `V` and a surjective étale morphism `V ⟶ Y` such that
each affine-space product of a pullback of `f` along `𝔸(n; V) ⟶ Y` is closed
on points; every DVR valuative square admits a finite separable dominating
discrete valuation ring extension with a lift; and every DVR valuative square
admits some dominating valuation-ring extension with a lift. -/
@[stacks 0H1Y] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.tfae_noetherian :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y],
    List.TFAE [UniversallyClosed f, ValuativeCriterion.Existence f,
      Closed.existsEtaleAffineSpace f, ValuativeCriterion.DVR.ExistsFiniteSeparableExtension f,
      ValuativeCriterion.DVR.ExistsExtension f])

/- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if it satisfies the existence part of the
valuative criterion. -/
#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existence_noetherian :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y],
    UniversallyClosed f ↔ ValuativeCriterion.Existence f)

/- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if every DVR valuative square admits a finite
separable dominating discrete valuation ring extension with a lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existsFiniteSeparableExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y],
    UniversallyClosed f ↔ ValuativeCriterion.DVR.ExistsFiniteSeparableExtension f)

/- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existsExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y],
    UniversallyClosed f ↔ ValuativeCriterion.DVR.ExistsExtension f)

/- A finite-type morphism into a locally Noetherian algebraic space that
satisfies DVR existence after a dominating extension is universally closed. -/
#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.of_existsExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.ExistsExtension f], UniversallyClosed f)

end UniversallyClosed

namespace ValuativeCriterion.Existence

/- A quasi-separated universally closed finite-type morphism into a locally Noetherian algebraic
space satisfies the existence part of the valuative criterion. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.of_universallyClosed_noetherian :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] [UniversallyClosed f],
    Existence f)

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
