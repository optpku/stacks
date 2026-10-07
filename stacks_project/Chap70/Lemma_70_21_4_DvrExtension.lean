module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
public import stacks_project.Chap69.Lemma_69_19_2_DVR

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

/-- A morphism of algebraic spaces satisfies existence of a dominating
valuation-ring extension with a lift on every valuative square whose ring is a
discrete valuation ring. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistsExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square admits a dominating valuation-ring extension with a
  lift. -/
  nonempty_extension :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension

namespace ValuativeCriterion.DVR.ExistsExtension

/-- The identity morphism of an algebraic space satisfies DVR existence after a
dominating extension. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : ExistsExtension (𝟙 X) := sorry

/-- Existence for all valuative squares implies existence after a dominating
extension on DVR valuative squares. -/
instance of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : ExistsExtension f := sorry

/-- A dotted lift on every DVR valuative square implies existence after a
dominating extension. -/
instance of_dvrExistence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f] : ExistsExtension f := sorry

/-- A morphism satisfies DVR existence after a dominating extension if and only if
every DVR valuative square admits such an extension. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ExistsExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension :=
  sorry

/-- Under `ExistsExtension f`, every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
theorem exists_extension {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [ExistsExtension f] (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R) :
    Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.DVR.ExistsExtension

/-- A morphism of algebraic spaces satisfies existence of a finite separable
dominating discrete valuation ring extension with a lift on every valuative
square whose ring is a discrete valuation ring. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistsFiniteSeparableExtension
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square admits a finite separable field extension, a
  dominating discrete valuation ring, and a lift of the extended square. -/
  exists_finiteSeparable :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      ∃ e : sq.Extension,
        FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
          IsDiscreteValuationRing e.R'

namespace ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

/-- The identity morphism of an algebraic space satisfies finite-separable DVR
existence after a dominating extension. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    ExistsFiniteSeparableExtension (𝟙 X) :=
  sorry

/-- Existence for all valuative squares implies finite-separable DVR existence
after a dominating extension. -/
instance of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : ExistsFiniteSeparableExtension f := sorry

/-- A dotted lift on every DVR valuative square implies finite-separable DVR
existence after a dominating extension. -/
instance of_dvrExistence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f] : ExistsFiniteSeparableExtension f :=
  sorry

/-- A morphism satisfies finite-separable DVR existence after a dominating
extension if and only if every DVR valuative square admits a finite separable
dominating discrete valuation ring extension with a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ExistsFiniteSeparableExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
        ∃ e : sq.Extension,
          FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' ∧
            IsDiscreteValuationRing e.R' :=
  sorry

end ValuativeCriterion.DVR.ExistsFiniteSeparableExtension

namespace ValuativeCriterion.DVR.ExistsExtension

/-- Finite-separable DVR existence after extension implies existence of some
dominating valuation-ring extension on DVR valuative squares. -/
instance of_existsFiniteSeparableExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [ExistsFiniteSeparableExtension f] : ExistsExtension f :=
  sorry

end ValuativeCriterion.DVR.ExistsExtension

end AlgebraicGeometry.AlgebraicSpace
