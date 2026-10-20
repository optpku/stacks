module

import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Limits.ExactFunctor
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Injectives
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Projectives
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w vA vB uA uB

variable {𝒜 : Type uA} {ℬ : Type uB}
  [Category.{vA} 𝒜] [Category.{vB} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [EnoughInjectives 𝒜]
  [PreservesFiniteLimits F]

/- Definition 64.6.4 (1). If F : 𝒜 ⥤ ℬ is left exact and 𝒜 has enough injectives,
the total right derived functor RF : D⁺(𝒜) ⥤ D⁺(ℬ) is
`Functor.rightDerivedFunctorPlus`. The source square with K⁺(ℐ) --F--> K⁺(ℬ)
is the Kan-extension unit `Functor.rightDerivedFunctorPlusUnit`, which is an
iso on HomotopyCategory.Plus (InjectiveObject 𝒜). -/
@[stacks 03T7] #check (CategoryTheory.Functor.rightDerivedFunctorPlusUnit_isIso_on_injectives F :
  ∀ X : HomotopyCategory.Plus (InjectiveObject 𝒜),
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι 𝒜).mapHomotopyCategoryPlus.obj X)))
#check (Functor.rightDerivedFunctorPlus F :
  DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
#check (Functor.rightDerivedFunctorPlusUnit F :
  F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ Functor.rightDerivedFunctorPlus F)

variable (G : 𝒜 ⥤ ℬ) [G.Additive] [EnoughProjectives 𝒜]
  [PreservesFiniteColimits G]

/- Definition 64.6.4 (2). If G : 𝒜 ⥤ ℬ is right exact and 𝒜 has enough projectives,
the total left derived functor LG : D⁻(𝒜) ⥤ D⁻(ℬ) is
`Functor.LeftDerived.Bounded.functor`. The source square with K⁻(𝒫) --G--> K⁻(ℬ)
is the Kan-extension counit `Functor.LeftDerived.Bounded.counit`, which is an
iso on projective complexes. -/
@[stacks 03T7] #check (CategoryTheory.Functor.LeftDerived.Bounded.counit_isIso_on_projectives G :
  ∀ X : HomotopyCategory.Minus.TermsIn 𝒜 (isProjective 𝒜),
    IsIso ((Functor.LeftDerived.Bounded.counit G).app
      ((HomotopyCategory.Minus.TermsIn.ι 𝒜).obj X)))
#check (Functor.LeftDerived.Bounded.functor G :
  DerivedCategory.Minus 𝒜 ⥤ DerivedCategory.Minus ℬ)
#check (Functor.LeftDerived.Bounded.counit G :
  DerivedCategory.Minus.Qh 𝒜 ⋙ Functor.LeftDerived.Bounded.functor G ⟶
    G.toBoundedAboveDerived)
