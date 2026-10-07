module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Displayed
public import ReasLib.CategoryTheory.DisplayedCategory.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment.Displayed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors from total finite right-derived realizations

The finite realization maps are indexed by the underlying bounded-below filtered complex.  The
displayed category records that dependency; this leaf totalizes it into an ordinary category and
maps the result to the generic filtered spectral-sequence realization category.  Thus downstream
code can use ordinary categorical composition while retaining the finite construction's chosen
resolution only at the source boundary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Realization

/-- The finite-to-generic displayed bridge preserves displayed identities after the canonical
identity-functor transport. -/
theorem displayedFunctor_map_id
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    DisplayedCategory.Hom.cast
        (FilteredComplex.SpectralSequence.Realization.WithAbutment.displayedCategory
          (Abutment.functor T))
        ((𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))).map_id K)
        ((Realization.Map.id S).toWithAbutmentMap) =
      (FilteredComplex.SpectralSequence.Realization.WithAbutment.displayedCategory
        (Abutment.functor T)).id S.toWithAbutment := sorry

/-- The finite-to-generic displayed bridge preserves displayed composition after the canonical
identity-functor transport. -/
theorem displayedFunctor_map_comp
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization T K} {R : Realization T L} {U : Realization T M}
    (m : Realization.Map f S R) (n : Realization.Map g R U) :
    DisplayedCategory.Hom.cast
        (FilteredComplex.SpectralSequence.Realization.WithAbutment.displayedCategory
          (Abutment.functor T))
        ((𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))).map_comp f g)
        ((Realization.Map.comp m n).toWithAbutmentMap) =
      (FilteredComplex.SpectralSequence.Realization.WithAbutment.displayedCategory
        (Abutment.functor T)).comp m.toWithAbutmentMap n.toWithAbutmentMap := sorry

/-- `[stacks 015W]` The displayed functor from finite right-derived realizations to generic
realizations retaining their functorial abutment comparisons. -/
@[stacks 015W "displayed finite right-derived realization functor"]
noncomputable def displayedFunctor
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    DisplayedFunctor (displayedCategory T)
      (FilteredComplex.SpectralSequence.Realization.WithAbutment.displayedCategory
        (Abutment.functor T))
      (𝟭 (CochainComplex.Plus (FilteredObject.Finite.category A))) where
  obj S := S.toWithAbutment
  map m := m.toWithAbutmentMap
  map_id := displayedFunctor_map_id T
  map_comp := displayedFunctor_map_comp T

/-- Totalizing `displayedFunctor` retains the filtered complex parameter and the functorial
abutment comparison. -/
@[stacks 015W "total finite right-derived realization functor with abutment"]
noncomputable def withAbutmentFunctor
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    Total T ⥤
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Total
        (Abutment.functor T) :=
  DisplayedFunctor.total (displayedFunctor T)

/-- The finite-to-generic total functor preserves the underlying bounded-below finite filtered
complex.  This functor-level equation is the base-projection API for downstream constructions. -/
@[stacks 015W "base projection of the total finite realization functor with abutment"]
theorem withAbutmentFunctor_forgetBase
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    withAbutmentFunctor T ⋙
        FilteredComplex.SpectralSequence.Realization.WithAbutment.forgetBase
          (Abutment.functor T) =
      Total.forgetBase T := sorry

/-- Object computation for the finite-to-generic displayed realization functor. -/
@[simp, stacks 015W "displayed finite right-derived realization functor"]
theorem displayedFunctor_obj
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S : Realization T K) :
    (displayedFunctor T).obj S = S.toWithAbutment := sorry

/-- Morphism computation for the finite-to-generic displayed realization functor. -/
@[simp, stacks 015W "displayed finite right-derived realization functor"]
theorem displayedFunctor_map
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {S : Realization T K} {R : Realization T L} (m : Realization.Map f S R) :
    (displayedFunctor T).map m = m.toWithAbutmentMap := sorry

/-- The base of an object under the abutment-preserving total functor is unchanged. -/
@[simp, stacks 015W "object computation for the total finite realization functor with abutment"]
theorem withAbutmentFunctor_obj_base
    (T : A ⥤ₗ B) [EnoughInjectives A]
    (S : Total T) :
    ((withAbutmentFunctor T).obj S).base = S.base := sorry

/-- The displayed object under the abutment-preserving total functor is the generic conversion. -/
@[simp, stacks 015W "object computation for the total finite realization functor with abutment"]
theorem withAbutmentFunctor_obj_obj
    (T : A ⥤ₗ B) [EnoughInjectives A]
    (S : Total T) :
    ((withAbutmentFunctor T).obj S).obj = S.obj.toWithAbutment := sorry

/-- The base morphism under the abutment-preserving total functor is unchanged. -/
@[simp, stacks 015W "map computation for the total finite realization functor with abutment"]
theorem withAbutmentFunctor_map_base
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Total T} (m : S ⟶ R) :
    ((withAbutmentFunctor T).map m).base = m.base := sorry

/-- The displayed morphism under the abutment-preserving total functor is the generic conversion
retaining its abutment square. -/
@[simp, stacks 015W "map computation for the total finite realization functor with abutment"]
theorem withAbutmentFunctor_map_displayed
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Total T} (m : S ⟶ R) :
    ((withAbutmentFunctor T).map m).displayed =
      m.displayed.toWithAbutmentMap := sorry

/-- `[stacks 015W]` Totalize the finite right-derived realization family and forget its
construction-specific resolution data to the generic realization category.  This functor is the
abutment-preserving totalization followed by the neutral forgetful functor. -/
@[stacks 015W "total finite right-derived realization functor"]
noncomputable def functor
    (T : A ⥤ₗ B) [EnoughInjectives A] :
    Total T ⥤
      FilteredComplex.SpectralSequence.Realization (C := B) :=
  withAbutmentFunctor T ⋙
    FilteredComplex.SpectralSequence.Realization.WithAbutment.forgetRealization
      (Abutment.functor T)

end Realization

/-- The total realization functor sends an object to the generic realization obtained by
forgetting its finite resolution witness. -/
@[simp, stacks 015W "object computation for the total finite realization functor"]
theorem Realization.functor_obj
    (T : A ⥤ₗ B) [EnoughInjectives A]
    (S : Realization.Total T) :
    (Realization.functor T).obj S = S.obj.toFilteredRealization := sorry

/-- The total realization functor sends a total morphism to the converted generic realization
map carried by its displayed component. -/
@[simp, stacks 015W "map computation for the total finite realization functor"]
theorem Realization.functor_map
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R : Realization.Total T}
    (m : S ⟶ R) :
    (Realization.functor T).map m = m.displayed.toFilteredMap := sorry

/-- The total realization functor maps an identity to the generic identity map. -/
@[simp, stacks 015W "identity computation for the total finite realization functor"]
theorem Realization.functor_map_id
    (T : A ⥤ₗ B) [EnoughInjectives A]
    (S : Realization.Total T) :
    (Realization.functor T).map (𝟙 S) =
      FilteredComplex.SpectralSequence.Realization.Map.id
        ((Realization.functor T).obj S) := sorry

/-- The total realization functor maps composition to generic realization composition. -/
@[simp, reassoc, stacks 015W "composition computation for the total finite realization functor"]
theorem Realization.functor_map_comp
    (T : A ⥤ₗ B) [EnoughInjectives A]
    {S R U : Realization.Total T}
    (m : S ⟶ R) (n : R ⟶ U) :
    (Realization.functor T).map (m ≫ n) =
      (Realization.functor T).map m ≫ (Realization.functor T).map n := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
