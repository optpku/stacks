/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightExact
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.FilteredObject.FiniteDerived

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory (GradedObject ℤ A)] [HasDerivedCategory (GradedObject ℤ B)]

section LeftExact

variable (T : A ⥤ₗ B) [EnoughInjectives A]

/- Definition 64.8.1 (1). If T : 𝒜 ⥤ₗ ℬ is left exact and 𝒜 has enough injectives,
the filtered derived functor RT : DF⁺(𝒜) ⥤ DF⁺(ℬ) is
`FilteredObject.FiniteDerived.Plus.LeftExact.functor`. Its defining square on
bounded-below filtered-injective homotopy complexes commutes by
`FilteredObject.FiniteDerived.Plus.LeftExact.diagramIso`. -/
@[stacks 03TD] #check
  (CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.functor T
    (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) :
    Plus.Category A (AssociatedGraded.inverts A) ⥤
      Plus.Category B (AssociatedGraded.inverts B))

#check (CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.injectiveHomotopy T :
  HomotopyCategory.Plus (FilteredObject.Finite.FilteredInjective.category A) ⥤
    HomotopyCategory.Plus (FilteredObject.Finite.category B))

#check (CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.diagramIso T
  (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) :
  Plus.FilteredInjective.functor A (AssociatedGraded.inverts A) ⋙
      Plus.LeftExact.functor T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ≅
    Plus.LeftExact.injectiveHomotopy T ⋙ Plus.Quotient.functor B (AssociatedGraded.inverts B))

end LeftExact

section RightExact

variable (G : A ⥤ᵣ B) [EnoughProjectives A]

/- Applying an additive functor to finite filtrations uses images of the mapped stage arrows. -/
#check (CategoryTheory.FilteredObject.Finite.imageMapFunctor :
  (F : A ⥤ B) → [F.Additive] → FilteredObject.Finite.category A ⥤
    FilteredObject.Finite.category B)

/- Definition 64.8.1 (2). If G : 𝒜 ⥤ᵣ ℬ is right exact and 𝒜 has enough projectives,
the filtered derived functor LG : DF⁻(𝒜) ⥤ DF⁻(ℬ) is
`FilteredObject.FiniteDerived.Minus.RightExact.functor`. The source square with
K⁻(P) --G--> K⁻(Filᶠ(ℬ)) is
`FilteredObject.FiniteDerived.Minus.RightExact.diagramIso`. The bottom arrow is
`FilteredObject.FiniteDerived.Minus.RightExact.homotopy`. -/
@[stacks 03TD] #check
  (CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact.functor G
    (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) :
    Minus.Category A (AssociatedGraded.inverts A) ⥤
      Minus.Category B (AssociatedGraded.inverts B))

#check (CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact.homotopy G :
  HomotopyCategory.Minus (FilteredObject.Finite.FilteredProjective.category A) ⥤
    HomotopyCategory.Minus (FilteredObject.Finite.category B))

#check (CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact.diagramIso G
  (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) :
  Minus.FilteredProjective.functor A (AssociatedGraded.inverts A) ⋙
      Minus.RightExact.functor G (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ≅
    Minus.RightExact.homotopy G ⋙ Minus.Quotient.functor B (AssociatedGraded.inverts B))

end RightExact
