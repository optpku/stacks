module

public import ReasLib.CategoryTheory.Filtration.Complex.KInjective.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Functor
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total

/-!
# Resolution projection from total unbounded right-derived realizations

Every realization retains a filtered K-injective resolution, and every realization map retains a
map of those resolutions.  This leaf packages those projections as displayed and ordinary
functors and exposes the comparison with the source filtered complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Forgetting a realization to its resolution preserves displayed identities after canonical
transport along the identity base functor. -/
@[stacks 0BKK "identity law for the realization-to-resolution displayed functor"]
theorem resolutionDisplayedFunctor_map_id
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K : FilteredComplex A} (S : Realization F K) :
    DisplayedCategory.Hom.cast
        (KInjectiveResolution.displayedCategory A)
        ((𝟭 (FilteredComplex A)).map_id K)
        ((Map.id F S).resolutionMap) =
      (KInjectiveResolution.displayedCategory A).id S.resolution := sorry

/-- Forgetting a realization to its resolution preserves displayed composition after canonical
transport along the identity base functor. -/
@[stacks 0BKK "composition law for the realization-to-resolution displayed functor"]
theorem resolutionDisplayedFunctor_map_comp
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : Realization F K} {S : Realization F L} {T : Realization F M}
    (m : Map F f R S) (n : Map F g S T) :
    DisplayedCategory.Hom.cast
        (KInjectiveResolution.displayedCategory A)
        ((𝟭 (FilteredComplex A)).map_comp f g)
        ((Map.comp F m n).resolutionMap) =
      (KInjectiveResolution.displayedCategory A).comp
        m.resolutionMap n.resolutionMap := sorry

/-- The displayed functor forgetting a realization to its selected filtered K-injective
resolution. -/
@[stacks 0BKK "displayed resolution projection from unbounded realizations"]
noncomputable def resolutionDisplayedFunctor
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    DisplayedFunctor (SpectralSequence.displayedCategory F)
      (KInjectiveResolution.displayedCategory A) (𝟭 (FilteredComplex A)) where
  obj S := S.resolution
  map m := m.resolutionMap
  map_id := resolutionDisplayedFunctor_map_id F
  map_comp := resolutionDisplayedFunctor_map_comp F

namespace Total

/-- Forget total realizations to total filtered K-injective resolutions. -/
@[stacks 0BKK "resolution projection from total unbounded realizations"]
noncomputable def resolutionFunctor
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    Total F ⥤ KInjectiveResolution.Total A :=
  DisplayedFunctor.total (resolutionDisplayedFunctor F)

/-- Total realization morphisms are determined by their base arrow and the morphism between the
selected filtered K-injective resolutions. -/
@[ext (iff := false), stacks 0BKK "extensionality through the resolution projection"]
theorem Hom.ext_resolutionMap
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Total F} {f g : S ⟶ T}
    (h_base : f.base = g.base)
    (h_resolution :
      KInjectiveResolution.Map.reindex h_base f.displayed.resolutionMap =
        g.displayed.resolutionMap) :
    f = g := sorry

/-- The resolution projection is faithful: its base and displayed resolution map recover a total
realization morphism. -/
@[stacks 0BKK "faithfulness of the realization resolution projection"]
noncomputable instance resolutionFunctor_faithful
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    (resolutionFunctor F).Faithful := sorry

/-- The total resolution projection commutes with the projections to source filtered
complexes. -/
@[stacks 0BKK "base projection of the realization resolution functor"]
theorem resolutionFunctor_forgetBase
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    resolutionFunctor F ⋙ KInjectiveResolution.Total.source A =
      Total.forgetBase F := sorry

/-- The resolving filtered complex carried by a total realization. -/
@[stacks 0BKK "resolving-complex projection from total unbounded realizations"]
noncomputable abbrev resolutionTarget
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    Total F ⥤ FilteredComplex A :=
  resolutionFunctor F ⋙ KInjectiveResolution.Total.target A

/-- The stored resolution comparisons are natural on total realization morphisms. -/
@[stacks 0BKK "naturality of resolution comparisons on total realizations"]
theorem resolutionComparison_naturality
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Total F} (m : S ⟶ T) :
    m.base ≫ T.obj.resolution.ι =
      S.obj.resolution.ι ≫ m.displayed.resolutionMap.hom := sorry

/-- The selected filtered K-injective comparisons form a natural transformation from each
source filtered complex to its resolving filtered complex. -/
@[stacks 0BKK "resolution comparison on total unbounded realizations"]
noncomputable def resolutionComparison
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] :
    Total.forgetBase F ⟶ resolutionTarget F where
  app S := S.obj.resolution.ι
  naturality _ _ m := resolutionComparison_naturality F m

end Total

/-- Object computation for the displayed resolution projection. -/
@[simp, stacks 0BKK "object of the displayed resolution projection"]
theorem resolutionDisplayedFunctor_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K : FilteredComplex A} (S : Realization F K) :
    (resolutionDisplayedFunctor F).obj S = S.resolution := sorry

/-- Morphism computation for the displayed resolution projection. -/
@[simp, stacks 0BKK "map of the displayed resolution projection"]
theorem resolutionDisplayedFunctor_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    (resolutionDisplayedFunctor F).map m = m.resolutionMap := sorry

namespace Total

/-- The total resolution projection preserves the base filtered complex. -/
@[simp, stacks 0BKK "base object of the total resolution projection"]
theorem resolutionFunctor_obj_base
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] (S : Total F) :
    ((resolutionFunctor F).obj S).base = S.base := sorry

/-- The displayed object of the total resolution projection is the selected resolution. -/
@[simp, stacks 0BKK "displayed object of the total resolution projection"]
theorem resolutionFunctor_obj_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] (S : Total F) :
    ((resolutionFunctor F).obj S).obj = S.obj.resolution := sorry

/-- The total resolution projection preserves the base morphism. -/
@[simp, stacks 0BKK "base map of the total resolution projection"]
theorem resolutionFunctor_map_base
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Total F} (m : S ⟶ T) :
    ((resolutionFunctor F).map m).base = m.base := sorry

/-- The displayed morphism of the total resolution projection is the stored resolution map. -/
@[simp, stacks 0BKK "displayed map of the total resolution projection"]
theorem resolutionFunctor_map_displayed
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Total F} (m : S ⟶ T) :
    ((resolutionFunctor F).map m).displayed = m.displayed.resolutionMap := sorry

/-- The resolving-complex projection evaluates to the selected resolving filtered complex. -/
@[simp, stacks 0BKK "object of the resolving-complex projection"]
theorem resolutionTarget_obj
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] (S : Total F) :
    (resolutionTarget F).obj S = S.obj.resolution.complex := sorry

/-- The resolving-complex projection maps by the stored resolution morphism. -/
@[simp, stacks 0BKK "map of the resolving-complex projection"]
theorem resolutionTarget_map
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F]
    {S T : Total F} (m : S ⟶ T) :
    (resolutionTarget F).map m = m.displayed.resolutionMap.hom := sorry

/-- A component of the total resolution comparison is the comparison stored by the selected
resolution. -/
@[simp, stacks 0BKK "component of the total realization resolution comparison"]
theorem resolutionComparison_app
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    [Functor.RightDerived.KInjective.HasDerived F] (S : Total F) :
    (resolutionComparison F).app S = S.obj.resolution.ι := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
