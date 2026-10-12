/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Remark_42_19_2_Pointwise
public import stacks_project.Chap42.Situation_42_7_1
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ChowGroup.Pointwise

/-- Remark 42.19.2: under Situation 42.7.1, if `X` is locally of finite type over `S` and
`k : ℤ`, there is a presentation
`⊕'_{δ(x)=k+1} K₁ᴹ(κ(x)) -∂→ ⊕'_{δ(x)=k} K₀ᴹ(κ(x)) → CH_k(X) → 0`.
Here `K₁ᴹ(κ(x)) = κ(x)ˣ` is the degree-one Milnor K-group of the residue field, `W_x`
is the reduced closure of `x`, and `∂(Σ f_x) = Σ (W_x ⟶ X)_* div(f_x)` in `Z_k(X)`,
which is identified with the primed `K₀ᴹ` product. Comparing with Definition 42.19.1
shows that this presents `CH_k(X)`. -/
@[stacks 0GU3]
theorem exact {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    (@complex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k).Exact ∧
      Epi (@complex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k).g := sorry

end AlgebraicGeometry.ChowGroup.Pointwise

open CycleGroup

#check MilnorK.degreeOneMap_bijective
#check Pointwise.equiv
