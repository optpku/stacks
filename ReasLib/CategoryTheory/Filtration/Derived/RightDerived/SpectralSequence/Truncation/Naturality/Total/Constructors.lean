module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructors for total truncation-filtration realizations

The selected representative lift remains inside `Realization.Map`; total-category construction
therefore needs only that canonical map owner and introduces no separate lift parameter.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Regard a truncation-filtration realization as an object of its total category. -/
@[stacks 0BKM "constructor for a total truncation-filtration realization"]
noncomputable abbrev of {K : DerivedCategory A} (S : Realization F K) :
    Realization.Total F where
  base := K
  obj := S

/-- The total truncation constructor retains the source derived object. -/
@[simp, stacks 0BKM "base computation for a total truncation realization"]
theorem of_base {K : DerivedCategory A} (S : Realization F K) :
    (of F S).base = K := sorry

/-- The total truncation constructor retains the supplied realization. -/
@[simp, stacks 0BKM "displayed computation for a total truncation realization"]
theorem of_obj {K : DerivedCategory A} (S : Realization F K) :
    (of F S).obj = S := sorry

namespace Hom

/-- Regard a truncation-filtration realization map as a morphism in the total category. -/
@[stacks 0BKM "constructor for a total truncation realization map"]
noncomputable abbrev ofMap {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    of F S ⟶ of F T where
  base := f
  displayed := m

/-- The base component of the constructed total truncation map is the supplied derived map. -/
@[simp, stacks 0BKM "base computation for a total truncation realization map"]
theorem ofMap_base {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).base = f := sorry

/-- The displayed component of the constructed total truncation map is the supplied map. -/
@[simp, stacks 0BKM "displayed computation for a total truncation realization map"]
theorem ofMap_displayed {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).displayed = m := sorry

/-- Construction of total truncation maps preserves identities. -/
@[simp, stacks 0BKM "identity computation for total truncation realization maps"]
theorem ofMap_id {K : DerivedCategory A} (S : Realization F K) :
    ofMap F (Realization.Map.id F S) = 𝟙 (of F S) := sorry

/-- Construction of total truncation maps preserves composition. -/
@[simp, stacks 0BKM "composition computation for total truncation realization maps"]
theorem ofMap_comp {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    ofMap F (Realization.Map.comp F m n) = ofMap F m ≫ ofMap F n := sorry

/-- Reindexing a truncation realization map leaves the constructed total morphism unchanged. -/
@[stacks 0BKM "reindexing computation for total truncation realization maps"]
theorem ofMap_reindex {K L : DerivedCategory A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    ofMap F (Realization.Map.reindex F h m) = ofMap F m := sorry

end Hom

/-- The truncation-to-generic functor sends a constructed total object to the total object of its
underlying generic realization. -/
@[simp, stacks 0BKM "generic image of a constructed total truncation realization"]
theorem genericFunctor_obj_of {K : DerivedCategory A} (S : Realization F K) :
    (genericFunctor F).obj (of F S) =
      RightDerived.SpectralSequence.Realization.Total.of F S.original := sorry

/-- The truncation-to-generic functor sends a constructed total map to the total map of its
underlying generic realization map. -/
@[simp, stacks 0BKM "generic image of a constructed total truncation realization map"]
theorem genericFunctor_map_ofMap {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (genericFunctor F).map (Hom.ofMap F m) =
      RightDerived.SpectralSequence.Realization.Total.Hom.ofMap F m.original := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
