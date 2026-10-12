/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Additivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.10.4: over a universally catenary scheme equipped with a dimension function
`δ`, the degree-`k` cycle associated to a coherent module sheaf is additive in a short exact
sequence on a locally finite type scheme when all three supports have `δ`-dimension at most
`k`. -/
@[stacks 02QZ] #check
  (AlgebraicGeometry.Scheme.Modules.associatedCycle_eq_add_of_shortExact :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) (C : ShortComplex X.Modules)
      [C.X₁.IsCoherent] [C.X₂.IsCoherent] [C.X₃.IsCoherent], C.ShortExact →
      (∀ x ∈ RingedSpace.moduleSupport C.X₁, f.relativeDimensionFunction δ x ≤ k) →
      (∀ x ∈ RingedSpace.moduleSupport C.X₂, f.relativeDimensionFunction δ x ≤ k) →
      (∀ x ∈ RingedSpace.moduleSupport C.X₃, f.relativeDimensionFunction δ x ≤ k) →
      @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₂ inferInstance
          (f.relativeDimensionFunction δ) k =
        @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₁ inferInstance
            (f.relativeDimensionFunction δ) k +
          @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₃ inferInstance
            (f.relativeDimensionFunction δ) k)

end AlgebraicGeometry.Scheme.Modules
