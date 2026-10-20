module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar annihilation for two-term derived objects

This file owns the cancellation principle for endomorphisms of two-term derived objects and its
specialization to scalar actions on derived modules.

@stack 0G9I
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.DerivedCategory.TwoTerm

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "Dᵃ" => _root_.DerivedCategory 𝒜
local notation "H" => _root_.DerivedCategory.homologyFunctor 𝒜

/-- An endomorphism of a two-term target vanishes if it vanishes after precomposition by a map
that is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`. -/
@[stacks 0G9I "two-term endomorphism cancellation"]
theorem endomorphism_eq_zero_of_comp_eq_zero
    {K K' : Dᵃ} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H 0).map α)) (hαneg1 : Epi ((H (-1)).map α))
    {γ : K' ⟶ K'} (hαγ : α ≫ γ = 0) :
    γ = 0 := sorry
/- Proof strategy: factor `α` and `γ` through the truncation triangles at degrees `-1` and `0`.
The isomorphism on `H⁰` kills the degree-zero component of `γ`, while epimorphy on `H⁻¹` kills
the degree-`-1` component; t-structure orthogonality for the remaining truncation pieces then
forces `γ = 0`. -/

end

section

variable {R : Type u} [CommRing R]

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "H" => _root_.DerivedCategory.homologyFunctor (ModuleCat R)

/-- Lemma 15.85.8: let `α : K ⟶ K'` be a morphism in `D(R)` between objects with
cohomology only in degrees `-1` and `0`. If `H⁰(α)` is an isomorphism and `H⁻¹(α)` is an
epimorphism, then every scalar acting by zero on `K` also acts by zero on `K'`. -/
@[stacks 0G9I "Lemma 15.85.8"]
theorem smul_id_eq_zero_of_homology
    {K K' : DMod} (α : K ⟶ K') (f : R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H 0).map α)) (hαneg1 : Epi ((H (-1)).map α))
    (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := sorry
/- Proof strategy: apply `endomorphism_eq_zero_of_comp_eq_zero` to `γ = f • 𝟙 K'`.  Naturality
and bilinearity give `α ≫ γ = f • α = (f • 𝟙 K) ≫ α`, which vanishes by `hf`. -/

end

end CategoryTheory.DerivedCategory.TwoTerm
