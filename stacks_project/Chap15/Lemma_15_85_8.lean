module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ScalarAnnihilation
import StacksCheckRecall

/-!
# Scalar annihilation for two-term complexes

Lemma 15.85.8 transfers the vanishing of a scalar action across a morphism that is an
isomorphism on `H⁰` and an epimorphism on `H⁻¹`.

@stack 0G9I
-/

@[expose] public section

open CategoryTheory

universe w v u

/- Lemma 15.85.8 (0G9I): for two-term objects `K` and `K'`, a scalar annihilating `K` also
annihilates `K'` under the stated homology hypotheses. -/

@[stacks 0G9I "Lemma 15.85.8"]
#check fun {R : Type u} [CommRing R]
    {K K' : DerivedCategory (ModuleCat R)} (α : K ⟶ K') (f : R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map α))
    (hαneg1 : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).map α))
    (hf : f • 𝟙 K = 0) =>
  (CategoryTheory.DerivedCategory.TwoTerm.smul_id_eq_zero_of_homology
      α f hKGE hKLE hK'GE hK'LE hα0 hαneg1 hf : f • 𝟙 K' = 0)

@[stacks 0G9I "two-term endomorphism cancellation"]
#check fun {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    {K K' : DerivedCategory 𝒜} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((DerivedCategory.homologyFunctor 𝒜 0).map α))
    (hαneg1 : Epi ((DerivedCategory.homologyFunctor 𝒜 (-1)).map α))
    {γ : K' ⟶ K'} (hαγ : α ≫ γ = 0) =>
  (CategoryTheory.DerivedCategory.TwoTerm.endomorphism_eq_zero_of_comp_eq_zero
      α hKGE hKLE hK'GE hK'LE hα0 hαneg1 hαγ : γ = 0)
