/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence

/-!
# Noetherian valuative tests for universal closedness

For a quasi-separated finite-type morphism of algebraic spaces into a locally
Noetherian target, universal closedness is equivalent to valuative existence,
closedness of affine-space tests on an étale atlas, and the two dominating DVR
extension criteria. Quasi-separatedness is required in the implication from
universal closedness to existence. The implication from DVR extension existence
to universal closedness requires no separation hypothesis.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- For a quasi-separated finite-type morphism of algebraic spaces over a scheme
with locally Noetherian target, universal closedness, valuative existence,
closedness of all affine-space product projections after a surjective étale
scheme atlas, finite-separable dominating DVR extensions with lifts, and
dominating valuation-ring extensions with lifts are equivalent. -/
theorem tfae_noetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] :
    List.TFAE [UniversallyClosed f, ValuativeCriterion.Existence f,
      Closed.existsEtaleAffineSpace f, ValuativeCriterion.DVR.ExistsFiniteSeparableExtension f,
      ValuativeCriterion.DVR.ExistsExtension f] :=
  sorry

/-- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if it satisfies the existence part of the
valuative criterion. -/
theorem iff_existence_noetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  UniversallyClosed.iff_existence f

/-- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if every DVR valuative square admits a finite
separable dominating discrete valuation ring extension with a lift. -/
theorem iff_existsFiniteSeparableExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] :
    UniversallyClosed f ↔ ValuativeCriterion.DVR.ExistsFiniteSeparableExtension f :=
  sorry

/-- A quasi-separated finite-type morphism into a locally Noetherian algebraic space is
universally closed if and only if every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
theorem iff_existsExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] :
    UniversallyClosed f ↔ ValuativeCriterion.DVR.ExistsExtension f :=
  sorry

/-- A finite-type morphism into a locally Noetherian algebraic space that
satisfies DVR existence after a dominating extension is universally closed. -/
instance of_existsExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.ExistsExtension f] : UniversallyClosed f :=
  sorry

end UniversallyClosed

namespace ValuativeCriterion.Existence

/-- A quasi-separated universally closed finite-type morphism into a locally Noetherian algebraic
space satisfies the existence part of the valuative criterion. -/
theorem of_universallyClosed_noetherian {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [IsLocallyNoetherian Y] [UniversallyClosed f] :
    Existence f :=
  ValuativeCriterion.Existence.of_universallyClosed f

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
