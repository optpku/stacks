/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_18_1_Invariant
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap79.«79_5_1_1_Section»
public import stacks_project.Chap79.«79_5_1_1_Infinitesimal»
public import stacks_project.Chap79.«79_5_1_1_Comparison»

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- 79.5.1.1 (1): For a groupoid in algebraic spaces and a first-order thickening
`ι : U₀ ⟶ U` of the object space, with `R₀ = s⁻¹(U₀)` and `e₀` the restricted
identity, each parameter `θ : Hom_{𝒪_{U₀}}(e₀^* Ω[s₀], Hom.conormalSheaf ι)`
determines a unique infinitesimal source section `δ` with `δ = θ · e`. -/
@[stacks 0CKE]
theorem existsUnique_infinitesimalSection_of_parameter {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι] (θ : Parameter G ι) :
    ∃! δ : InfinitesimalSection G ι, IsPerturbation G ι θ δ :=
  sorry

/-- 79.5.1.1 (2): If `U₀` is `R`-invariant, every infinitesimal source section
arises from a unique parameter, so the relation `IsPerturbation` is a bijection
between `Hom_{𝒪_{U₀}}(e₀^* Ω[s₀], Hom.conormalSheaf ι)` and `Γ₀`. -/
@[stacks 0CKE]
theorem isPerturbation_bijective {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι]
    (h_invariant : G.toPreRelation.IsInvariant (Subobject.mk ι))
    (δ : InfinitesimalSection G ι) :
    ∃! θ : Parameter G ι, IsPerturbation G ι θ δ :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
