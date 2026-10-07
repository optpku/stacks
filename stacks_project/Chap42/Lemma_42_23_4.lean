module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Lemma 42.23.4: For a scheme locally of finite type over a universally catenary scheme with
dimension function `δ`, there is a canonical map from `CH_k(X)` to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))`. -/
@[stacks 0FDS] #check
  (AlgebraicGeometry.ChowGroup.toFilteredK0 f δ k :
    @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      AlgebraicGeometry.Scheme.Modules.FilteredK0 f δ (k + 1) (k - 1))
