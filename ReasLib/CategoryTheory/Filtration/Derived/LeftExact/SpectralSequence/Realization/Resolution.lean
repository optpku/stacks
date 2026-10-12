/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Functor
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Displayed

/-!
# Forgetting finite right-derived realizations to resolutions

Finite right-derived realizations retain a strict filtered-injective resolution and their maps
retain the corresponding resolution map.  This leaf packages those projections as a displayed
functor and as its induced functor on total categories.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Forgetting a realization to its resolution preserves displayed identities after transport
along the identity base functor. -/
theorem resolutionDisplayedFunctor_map_id
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    DisplayedCategory.Hom.cast
        (Resolution.displayedCategory A)
        ((𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))).map_id K)
        ((Map.id S).resolutionMap) =
      (Resolution.displayedCategory A).id S.resolution := sorry

/-- Forgetting a realization to its resolution preserves displayed composition after transport
along the identity base functor. -/
theorem resolutionDisplayedFunctor_map_comp
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T K} {R : Realization T L} {U : Realization T M}
    (m : Map f S R) (n : Map g R U) :
    DisplayedCategory.Hom.cast
        (Resolution.displayedCategory A)
        ((𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))).map_comp f g)
        ((Map.comp m n).resolutionMap) =
      (Resolution.displayedCategory A).comp m.resolutionMap n.resolutionMap := sorry

/-- The displayed functor forgetting a finite right-derived realization to its chosen strict
filtered-injective resolution. -/
@[stacks 015W "forgetful displayed functor from finite realizations to resolutions"]
noncomputable def resolutionDisplayedFunctor
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    DisplayedFunctor (displayedCategory T) (Resolution.displayedCategory A)
      (𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))) where
  obj S := S.resolution
  map m := m.resolutionMap
  map_id := resolutionDisplayedFunctor_map_id T
  map_comp := resolutionDisplayedFunctor_map_comp T

/-- The functor forgetting total finite realizations to total strict filtered-injective
resolutions. -/
@[stacks 015W "forgetful functor from total finite realizations to total resolutions"]
noncomputable def resolutionFunctor
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    Total T ⥤ Resolution.Total A :=
  DisplayedFunctor.total (resolutionDisplayedFunctor T)

/-- The total resolution forgetful functor commutes with the projections to the bounded-below
finite filtered source complex. -/
@[stacks 015W "base projection of the total resolution forgetful functor"]
theorem resolutionFunctor_forgetBase
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    resolutionFunctor T ⋙ Resolution.Total.source A = Total.forgetBase T := sorry

/-- Object computation for the displayed resolution forgetful functor. -/
@[simp, stacks 015W "forgetful displayed functor from finite realizations to resolutions"]
theorem resolutionDisplayedFunctor_obj
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    (resolutionDisplayedFunctor T).obj S = S.resolution := sorry

/-- Morphism computation for the displayed resolution forgetful functor. -/
@[simp, stacks 015W "forgetful displayed functor from finite realizations to resolutions"]
theorem resolutionDisplayedFunctor_map
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Map f S R) :
    (resolutionDisplayedFunctor T).map m = m.resolutionMap := sorry

/-- The total resolution forgetful functor preserves the base complex. -/
@[simp, stacks 015W "forgetful functor from total finite realizations to total resolutions"]
theorem resolutionFunctor_obj_base
    (T : A ⥤ₗ B) [EnoughInjectives A] (S : Total T) :
    ((resolutionFunctor T).obj S).base = S.base := sorry

/-- The displayed object of the total resolution forgetful functor is the chosen resolution. -/
@[simp, stacks 015W "forgetful functor from total finite realizations to total resolutions"]
theorem resolutionFunctor_obj_obj
    (T : A ⥤ₗ B) [EnoughInjectives A] (S : Total T) :
    ((resolutionFunctor T).obj S).obj = S.obj.resolution := sorry

/-- The total resolution forgetful functor preserves the base morphism. -/
@[simp, stacks 015W "forgetful functor from total finite realizations to total resolutions"]
theorem resolutionFunctor_map_base
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Total T} (m : S ⟶ R) :
    ((resolutionFunctor T).map m).base = m.base := sorry

/-- The displayed morphism of the total resolution forgetful functor is the stored resolution
map. -/
@[simp, stacks 015W "forgetful functor from total finite realizations to total resolutions"]
theorem resolutionFunctor_map_displayed
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Total T} (m : S ⟶ R) :
    ((resolutionFunctor T).map m).displayed = m.displayed.resolutionMap := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization
