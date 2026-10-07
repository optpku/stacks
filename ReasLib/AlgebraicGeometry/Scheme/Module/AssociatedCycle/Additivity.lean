module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact

/-!
# Additivity of associated cycles

The cycle associated to a coherent module sheaf is additive along a short exact sequence when
the supports of all three terms have the prescribed dimension bound.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a universally catenary scheme equipped with a dimension function, the degree-`k`
cycle associated to a coherent module sheaf is additive in a short exact sequence on a locally
finite-type scheme when all three supports have dimension at most `k`. -/
theorem associatedCycle_eq_add_of_shortExact
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) (C : ShortComplex X.Modules)
    [C.X₁.IsCoherent] [C.X₂.IsCoherent] [C.X₃.IsCoherent] (hC : C.ShortExact)
    (h₁ : ∀ x ∈ RingedSpace.moduleSupport C.X₁, f.relativeDimensionFunction δ x ≤ k)
    (h₂ : ∀ x ∈ RingedSpace.moduleSupport C.X₂, f.relativeDimensionFunction δ x ≤ k)
    (h₃ : ∀ x ∈ RingedSpace.moduleSupport C.X₃, f.relativeDimensionFunction δ x ≤ k) :
    @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₂ inferInstance
        (f.relativeDimensionFunction δ) k =
      @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₁ inferInstance
          (f.relativeDimensionFunction δ) k +
        @associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) C.X₃ inferInstance
          (f.relativeDimensionFunction δ) k := sorry

end AlgebraicGeometry.Scheme.Modules
