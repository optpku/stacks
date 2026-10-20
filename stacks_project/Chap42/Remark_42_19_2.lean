module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Pointwise

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.19.2: under Situation 42.7.1, if `X` is locally of finite type over `S` and
`k : ℤ`, there is a presentation
`⊕'_{δ(x)=k+1} K₁ᴹ(κ(x)) -∂→ ⊕'_{δ(x)=k} K₀ᴹ(κ(x)) → CH_k(X) → 0`.
Here `K₁ᴹ(κ(x)) = κ(x)ˣ` is the degree-one Milnor K-group of the residue field, `W_x`
is the reduced closure of `x`, and `∂(Σ f_x) = Σ (W_x ⟶ X)_* div(f_x)` in `Z_k(X)`,
which is identified with the primed `K₀ᴹ` product. Comparing with Definition 42.19.1
shows that this presents `CH_k(X)`. -/
@[stacks 0GU3] #check (AlgebraicGeometry.ChowGroup.Pointwise.exact :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ),
    (@AlgebraicGeometry.ChowGroup.Pointwise.complex X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k).Exact ∧
      Epi (@AlgebraicGeometry.ChowGroup.Pointwise.complex X
        (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k).g)

#check (AlgebraicGeometry.CycleGroup.Pointwise.equiv :
  ∀ {X : Scheme.{u}} (d : X → ℤ) (k : ℤ),
    CycleGroup X d k ≃+ AlgebraicGeometry.CycleGroup.Pointwise.locallyFinite d k)
