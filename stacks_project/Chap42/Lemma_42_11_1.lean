/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.DimensionFunction
import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 42.11.1: a morphism between integral schemes of equal `δ`-dimension over `S`
either has range in a proper closed subscheme or is dominant with finite function-field
extension. -/
@[stacks 02R1] #check
  (AlgebraicGeometry.Scheme.Hom.range_subset_properClosed_or_finiteFunctionFieldExtension :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [hXint : IsIntegral X.left] [hYint : IsIntegral Y.left] (f : X ⟶ Y),
      X.hom.relativeDimensionFunction δ (genericPoint X.left) =
          Y.hom.relativeDimensionFunction δ (genericPoint Y.left) →
        (∃ Z : Y.left.IdealSheafData,
          Z.support ≠ ⊤ ∧ Set.range f.left ⊆ (Z.support : Set Y.left)) ∨
          ∃ hdom : IsDominant f.left,
            @FiniteFunctionFieldExtension _ _ f.left hXint hYint hdom)

end AlgebraicGeometry.Scheme.Hom
