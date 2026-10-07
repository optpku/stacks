module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# DVR existence after dominating extensions for algebraic stacks

A morphism of algebraic stacks may satisfy existence in the valuative criterion
after replacing a discrete valuation ring by a dominating valuation ring.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks satisfies existence of a dominating
valuation-ring extension with a lift on every valuative square whose ring is a
discrete valuation ring. -/
@[mk_iff]
class ValuativeCriterion.DVR.ExistsExtension {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every DVR valuative square admits a dominating valuation-ring extension with a
  lift. -/
  nonempty_extension :
    ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension

namespace ValuativeCriterion.DVR.ExistsExtension

/-- The identity morphism of an algebraic stack satisfies DVR existence after a
dominating extension. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    ExistsExtension (𝟙 X) :=
  sorry

/-- Existence for all valuative squares implies existence after a dominating
extension on DVR valuative squares. -/
instance of_existence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : ExistsExtension f :=
  sorry

/-- A morphism satisfies DVR existence after a dominating extension if and only if
every DVR valuative square admits such an extension. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    ExistsExtension f ↔
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension :=
  sorry

/-- Under `ExistsExtension f`, every DVR valuative square admits a dominating
valuation-ring extension with a lift. -/
theorem exists_extension {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    [AlgebraicStack X] [AlgebraicStack Y] [ExistsExtension f]
    (sq : ValuativeCommSq f) (hR : IsDiscreteValuationRing sq.R) :
    Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.DVR.ExistsExtension

end AlgebraicGeometry.AlgebraicStack
