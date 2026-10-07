module

public import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveComparison
public import ReasLib.CategoryTheory.DerivedCategory.ProjectiveResolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Lemma 64.6.3 (1). Let `I` be in `Comp⁺(𝒜)` with injective terms. Then
`Hom` in `D(𝒜)` from any `K` into `I` agrees with `Hom` in `K(𝒜)`. -/
@[stacks 03T6] #check (CochainComplex.InjectivePlus.toDerived_map_bijective :
  ∀ (K : CochainComplex 𝒜 ℤ) (I : CochainComplex.InjectivePlus 𝒜),
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I) →
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I))))
#check CochainComplex.IsKInjective.Qh_map_bijective

/- Lemma 64.6.3 (2). Let `P` be in `Comp⁻(𝒜)` with projective terms. Then
`Hom` in `D(𝒜)` out of `P` into any `K` agrees with `Hom` in `K(𝒜)`. -/
@[stacks 03T6] #check (CochainComplex.ProjectiveMinus.toDerived_map_bijective :
  ∀ (P : CochainComplex.ProjectiveMinus 𝒜) (K : CochainComplex 𝒜 ℤ),
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj P ⟶
        (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K) →
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj P) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K))))
#check CochainComplex.IsKProjective.Qh_map_bijective

section Injective

variable [EnoughInjectives 𝒜]

#check (CategoryTheory.HomotopyCategory.Plus.Injective.toDerived 𝒜 :
  HomotopyCategory.Plus.Injective 𝒜 ⥤ DerivedCategory.Plus 𝒜)

/- Lemma 64.6.3 (3). If `𝒜` has enough injectives and `ℐ ⊂ 𝒜` is the additive
subcategory of injectives, then `D⁺(𝒜) ≅ K⁺(ℐ)` as triangulated categories. -/
@[stacks 03T6] #check
  (CategoryTheory.HomotopyCategory.Plus.Injective.toDerived.isEquivalence :
    Functor.IsEquivalence (CategoryTheory.HomotopyCategory.Plus.Injective.toDerived 𝒜))
#check (CategoryTheory.HomotopyCategory.Plus.Injective.toDerived.isTriangulated 𝒜 :
  Functor.IsTriangulated (CategoryTheory.HomotopyCategory.Plus.Injective.toDerived 𝒜))

end Injective

section Projective

variable [EnoughProjectives 𝒜]

#check (CategoryTheory.HomotopyCategory.Minus.Projective.toDerived 𝒜 :
  HomotopyCategory.Minus.TermsIn 𝒜 (isProjective 𝒜) ⥤ DerivedCategory.Minus 𝒜)

/- Lemma 64.6.3 (4). If `𝒜` has enough projectives and `𝒫 ⊂ 𝒜` is the additive
subcategory of projectives, then `D⁻(𝒜) ≅ K⁻(𝒫)`. -/
@[stacks 03T6] #check
  (CategoryTheory.HomotopyCategory.Minus.Projective.toDerived.isEquivalence :
    Functor.IsEquivalence (CategoryTheory.HomotopyCategory.Minus.Projective.toDerived 𝒜))

end Projective
