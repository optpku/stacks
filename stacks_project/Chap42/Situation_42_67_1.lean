module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Situation 42.67.1: A flat morphism is compatible with dimension functions up to the
integer shift `c` when `δ' (g.fiberι s s') = δ s + c` at every generic point `s'` of every
fiber over `s`. -/
@[stacks 0FVG] #check
  (AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S'],
      (g : S' ⟶ S) → [Flat g] → (δ : S → ℤ) → [IsDimensionFunction δ] →
      (δ' : S' → ℤ) → [IsDimensionFunction δ'] → ℤ → Prop)

end AlgebraicGeometry.Scheme.Hom
