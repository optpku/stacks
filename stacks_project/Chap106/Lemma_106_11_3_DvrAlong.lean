/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap101.Lemma_101_39_12_Existence
public import stacks_project.Chap106.Lemma_106_11_3_FactorsThrough

/-!
# DVR existence after dominating extensions along a morphism of algebraic stacks

A morphism of algebraic stacks satisfies existence in the valuative criterion
along a second morphism when every DVR valuative 2-square whose generic
1-morphism factors through that morphism admits a dominating valuation-ring
extension with a nonempty dotted-arrow category.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCriterion.DVR.Along

/-- Every valuative 2-square whose generic 1-morphism factors through `h` and
whose ring is a discrete valuation ring admits a field extension and a
dominating valuation ring with a nonempty dotted-arrow category. -/
def ExistsExtension {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f,
    IsDiscreteValuationRing sq.sq.R → Nonempty sq.sq.Extension

/-- Restricted DVR existence after a dominating extension is equivalent to every
factored DVR valuative 2-square having a nonempty dotted-arrow category after
extension. -/
theorem existsExtension_iff {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y) :
    ExistsExtension h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Nonempty sq.sq.Extension :=
  sorry

/-- Restricted DVR existence after a dominating extension follows from a nonempty
dotted-arrow category after extension on every factored DVR valuative 2-square. -/
theorem of {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y}
    (h_existence :
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Nonempty sq.sq.Extension) :
    ExistsExtension h f :=
  sorry

/-- Restricted DVR existence after a dominating extension supplies a nonempty
dotted-arrow category of a factored DVR valuative 2-square. -/
theorem exists_extension {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (h_existence : ExistsExtension h f)
    (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R) :
    Nonempty sq.sq.Extension :=
  sorry

/-- Unrestricted DVR existence after a dominating extension implies existence
along any morphism. -/
theorem of_dvrExistsExtension {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y)
    (h_existence :
      ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R → Nonempty sq.Extension) :
    ExistsExtension h f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicStack
