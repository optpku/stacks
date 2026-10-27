/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Existence

/-!
# DVR existence after dominating extensions

A morphism of algebraic spaces may satisfy existence in the valuative criterion
after replacing a discrete valuation ring by a dominating valuation ring, or by
a finite separable discrete valuation ring extension.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.21.4: a morphism of algebraic spaces satisfies existence of a dominating
valuation-ring extension with a lift on every valuative square whose ring is a
discrete valuation ring. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

namespace ValuativeCriterion.DVR.ExistsExtension

/- The identity morphism of an algebraic space satisfies DVR existence after a
dominating extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, ExistsExtension (𝟙 X))

/- Existence for all valuative squares implies existence after a dominating
extension on DVR valuative squares. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.of_existence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f], ExistsExtension f)

/- A dotted lift on every DVR valuative square implies existence after a
dominating extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.of_dvrExistence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f], ExistsExtension f)

/- A morphism satisfies DVR existence after a dominating extension if and only if
every DVR valuative square admits such an extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ExistsExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension)

/- Under `ExistsExtension f`, every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.exists_extension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [ExistsExtension f] (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R),
    Nonempty sq.Extension)

end ValuativeCriterion.DVR.ExistsExtension

/- A morphism of algebraic spaces satisfies existence of a finite separable
dominating discrete valuation ring extension with a lift on every valuative
square whose ring is a discrete valuation ring. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsFiniteSeparableExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

namespace ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

/- The identity morphism of an algebraic space satisfies finite-separable DVR
existence after a dominating extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsFiniteSeparableExtension.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, ExistsFiniteSeparableExtension (𝟙 X))

/- Existence for all valuative squares implies finite-separable DVR existence
after a dominating extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsFiniteSeparableExtension.of_existence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f], ExistsFiniteSeparableExtension f)

/- A dotted lift on every DVR valuative square implies finite-separable DVR
existence after a dominating extension. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsFiniteSeparableExtension.of_dvrExistence :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f], ExistsFiniteSeparableExtension f)

/- A morphism satisfies finite-separable DVR existence after a dominating
extension if and only if every DVR valuative square admits a finite separable
dominating discrete valuation ring extension with a lift. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsFiniteSeparableExtension.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    ExistsFiniteSeparableExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        ∃ e : sq.Extension,
          FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
            IsDiscreteValuationRing e.R')

end ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

namespace ValuativeCriterion.DVR.ExistsExtension

/- Finite-separable DVR existence after extension implies existence of some
dominating valuation-ring extension on DVR valuative squares. -/
#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.ExistsExtension.of_existsFiniteSeparableExtension :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [ExistsFiniteSeparableExtension f], ExistsExtension f)

end ValuativeCriterion.DVR.ExistsExtension

end AlgebraicGeometry.AlgebraicSpace
