module

public import ReasLib.CategoryTheory.DisplayedCategory.Functor
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Displayed
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Forget

/-!
# Total category of stupid-filtration realizations

The stupid-filtration specialization has a canonical base functor into filtered complexes.  This
leaf packages the resulting displayed and total functors and reuses the generic right-derived
realization projections.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

namespace Realization

/-- The total category of cochain complexes equipped with stupid-filtration realizations. -/
@[stacks 0FLK "total category of stupid-filtration realizations"]
abbrev Total
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :=
  DisplayedCategory.Total (displayedCategory F)

namespace Total

/-- Forget a total stupid-filtration realization to its source cochain complex. -/
@[stacks 0FLK "base of a total stupid-filtration realization"]
abbrev forgetBase
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    Total F ⥤ CochainComplex A ℤ :=
  DisplayedCategory.Total.forget (displayedCategory F)

/-- The source of a total stupid-filtration realization is its stored cochain complex. -/
@[simp, stacks 0FLK "base of a total stupid-filtration realization"]
theorem forgetBase_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    (forgetBase F).obj S = S.base := sorry

/-- The base map of a total stupid-filtration realization morphism is its stored cochain map. -/
@[simp, stacks 0FLK "base map of a total stupid-filtration realization"]
theorem forgetBase_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    (forgetBase F).map m = m.base := sorry

end Total

/-- Forgetting a stupid-filtration realization to its generic realization preserves displayed
identities after transport along the stupid-filtration functor. -/
@[stacks 0FLK "identity law for the stupid-to-generic displayed functor"]
theorem genericDisplayedFunctor_map_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K : CochainComplex A ℤ} (S : Realization F K) :
    DisplayedCategory.Hom.cast
        (RightDerived.SpectralSequence.displayedCategory F)
        ((CochainComplex.Stupid.functor (A := A)).map_id K)
        ((Map.id F S).original) =
      (RightDerived.SpectralSequence.displayedCategory F).id S.original := sorry

/-- Forgetting a stupid-filtration realization to its generic realization preserves displayed
composition after transport along the stupid-filtration functor. -/
@[stacks 0FLK "composition law for the stupid-to-generic displayed functor"]
theorem genericDisplayedFunctor_map_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {R : Realization F K} {S : Realization F L} {T : Realization F M}
    (m : Map F f R S) (n : Map F g S T) :
    DisplayedCategory.Hom.cast
        (RightDerived.SpectralSequence.displayedCategory F)
        ((CochainComplex.Stupid.functor (A := A)).map_comp f g)
        ((Map.comp F m n).original) =
      (RightDerived.SpectralSequence.displayedCategory F).comp
        m.original n.original := sorry

/-- The displayed functor from stupid-filtration realizations to generic filtered realizations. -/
@[stacks 0FLK "displayed stupid-to-generic realization functor"]
noncomputable def genericDisplayedFunctor
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    DisplayedFunctor (displayedCategory F)
      (RightDerived.SpectralSequence.displayedCategory F)
      (CochainComplex.Stupid.functor (A := A)) where
  obj S := S.original
  map m := m.original
  map_id := genericDisplayedFunctor_map_id F
  map_comp := genericDisplayedFunctor_map_comp F

namespace Total

/-- The total functor from stupid-filtration realizations to generic filtered realizations. -/
@[stacks 0FLK "total stupid-to-generic realization functor"]
noncomputable def genericFunctor
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    Total F ⥤ RightDerived.SpectralSequence.Realization.Total F :=
  DisplayedFunctor.total (genericDisplayedFunctor F)

/-- The total stupid-to-generic functor commutes with the source projections. -/
@[stacks 0FLK "base projection of the total stupid-to-generic functor"]
theorem genericFunctor_forgetBase
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    genericFunctor F ⋙ RightDerived.SpectralSequence.Realization.Total.forgetBase F =
      Total.forgetBase F ⋙ CochainComplex.Stupid.functor (A := A) := sorry

/-- The base object of the total stupid-to-generic functor. -/
@[simp, stacks 0FLK "base object of the total stupid-to-generic functor"]
theorem genericFunctor_obj_base
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    ((genericFunctor F).obj S).base =
      (CochainComplex.Stupid.functor (A := A)).obj S.base := sorry

/-- The displayed object of the total stupid-to-generic functor. -/
@[simp, stacks 0FLK "displayed object of the total stupid-to-generic functor"]
theorem genericFunctor_obj_displayed
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    ((genericFunctor F).obj S).obj = S.obj.original := sorry

/-- The base map of the total stupid-to-generic functor. -/
@[simp, stacks 0FLK "base map of the total stupid-to-generic functor"]
theorem genericFunctor_map_base
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    ((genericFunctor F).map m).base =
      (CochainComplex.Stupid.functor (A := A)).map m.base := sorry

/-- The displayed map of the total stupid-to-generic functor. -/
@[simp, stacks 0FLK "displayed map of the total stupid-to-generic functor"]
theorem genericFunctor_map_displayed
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    ((genericFunctor F).map m).displayed = m.displayed.original := sorry

/-- The total stupid-to-generic functor is faithful because the generic map is the data owner. -/
@[stacks 0FLK "faithfulness of the stupid-to-generic realization functor"]
noncomputable instance genericFunctor_faithful
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    (genericFunctor F).Faithful := sorry

/-- Forget a total stupid-filtration realization to its filtered right-derived model. -/
@[stacks 0FLK "filtered-model projection from total stupid realizations"]
noncomputable abbrev forgetFiltered
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    Total F ⥤ FilteredComplex B :=
  genericFunctor F ⋙ RightDerived.SpectralSequence.Realization.Total.forgetFiltered F

/-- Forget a total stupid-filtration realization to its spectral sequence. -/
@[stacks 0FLK "spectral-sequence projection from total stupid realizations"]
noncomputable abbrev forgetSequence
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    Total F ⥤ CohomologicalSpectralSequence B 0 :=
  genericFunctor F ⋙ RightDerived.SpectralSequence.Realization.Total.forgetSequence F

/-- Forget a total stupid-filtration realization to the underlying cochain complex of its model. -/
@[stacks 0FLK "underlying-complex projection from total stupid realizations"]
noncomputable abbrev forgetUnderlying
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A] :
    Total F ⥤ CochainComplex B ℤ :=
  forgetFiltered F ⋙ FilteredComplex.underlyingFunctor

/-- The filtered-model projection of a total stupid realization evaluates to its stored model. -/
@[simp, stacks 0FLK "filtered model of a total stupid realization"]
theorem forgetFiltered_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    (forgetFiltered F).obj S = S.obj.filtered := sorry

/-- The filtered-model projection maps by the filtered component of a stupid realization map. -/
@[simp, stacks 0FLK "filtered map of a total stupid realization"]
theorem forgetFiltered_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    (forgetFiltered F).map m = m.displayed.filteredMap := sorry

/-- The spectral-sequence projection of a total stupid realization evaluates to its stored
sequence. -/
@[simp, stacks 0FLK "sequence of a total stupid realization"]
theorem forgetSequence_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    (forgetSequence F).obj S = S.obj.sequence := sorry

/-- The spectral-sequence projection maps by the sequence component of a stupid realization map. -/
@[simp, stacks 0FLK "sequence map of a total stupid realization"]
theorem forgetSequence_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    (forgetSequence F).map m = m.displayed.sequenceMap := sorry

/-- The underlying-complex projection of a total stupid realization evaluates to the underlying
complex of its filtered model. -/
@[simp, stacks 0FLK "underlying complex of a total stupid realization"]
theorem forgetUnderlying_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    (S : Total F) :
    (forgetUnderlying F).obj S = S.obj.filtered.underlying := sorry

/-- The underlying-complex projection maps by the underlying filtered map. -/
@[simp, stacks 0FLK "underlying map of a total stupid realization"]
theorem forgetUnderlying_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]
    {S T : Total F} (m : S ⟶ T) :
    (forgetUnderlying F).map m =
      FilteredComplex.underlyingMap m.displayed.filteredMap := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization
