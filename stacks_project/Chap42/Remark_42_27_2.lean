module

public import ReasLib.AlgebraicGeometry.ChowGroup.MilnorComplex
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.27.2: under Situation 42.7.1, if `X` is locally of finite type over `S` and
`k : ℤ`, there is a complex
`⊕'_{δ(x)=k+2} K₂ᴹ(κ(x)) -∂→ ⊕'_{δ(x)=k+1} K₁ᴹ(κ(x)) -∂→ ⊕'_{δ(x)=k} K₀ᴹ(κ(x))`.
Here `K₂ᴹ(κ(x))` is the degree-two Milnor K-group of the residue field, presented as the
quotient of `κ(x)ˣ ⊗ κ(x)ˣ` by the Steinberg tensors `λ ⊗ (1-λ)`, the first `∂` is the tame
symbol `∂_{O_{W_x, x'}}` along immediate specializations with `δ(x') = k+1`, and the second
`∂` is the boundary of Remark 42.19.2 landed in the primed `K₀ᴹ` product. -/
@[stacks 0GU9] #check (AlgebraicGeometry.ChowGroup.milnorComplex :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ), ShortComplex Ab)
