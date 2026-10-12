/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/- Lemma 42.67.2: Under a flat base change compatible with dimension functions up to
the shift `c`, every irreducible component of the base change of an integral scheme of
`δ`-dimension `k` has `δ'`-dimension `k + c`. -/
@[stacks 0FVH] #check
  (AlgebraicGeometry.Scheme.Hom.deltaDimension_pullback_component :
    ∀ {S S' X : Scheme.{u}}
      [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
      (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
      (f : X ⟶ S) [LocallyOfFiniteType f] [IsIntegral X] (k : ℤ)
      (hX : f.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) = k)
      (Z' : irreducibleComponents (pullback f g : Scheme)),
      (pullback.snd f g).deltaDimension δ'
        (toIrreducibleCloseds (genericPoints.ofComponent Z')) = k + c)

end Hom
end Scheme
end AlgebraicGeometry
