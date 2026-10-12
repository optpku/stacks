/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructors for total stupid-filtration realizations

These constructors let downstream code enter the total category from the semantic realization
and map owners without mentioning displayed-category structure fields.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Regard a stupid-filtration realization as an object of its total category. -/
@[stacks 0FLK "constructor for a total stupid-filtration realization"]
noncomputable abbrev of {K : CochainComplex A ℤ} (S : Realization F K) :
    Realization.Total F where
  base := K
  obj := S

/-- The total stupid constructor retains the source cochain complex. -/
@[simp, stacks 0FLK "base computation for a total stupid realization"]
theorem of_base {K : CochainComplex A ℤ} (S : Realization F K) :
    (of F S).base = K := sorry

/-- The total stupid constructor retains the supplied realization. -/
@[simp, stacks 0FLK "displayed computation for a total stupid realization"]
theorem of_obj {K : CochainComplex A ℤ} (S : Realization F K) :
    (of F S).obj = S := sorry

namespace Hom

/-- Regard a stupid-filtration realization map as a morphism in the total category. -/
@[stacks 0FLK "constructor for a total stupid realization map"]
noncomputable abbrev ofMap {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    of F S ⟶ of F T where
  base := f
  displayed := m

/-- The base component of the constructed total stupid map is the supplied cochain map. -/
@[simp, stacks 0FLK "base computation for a total stupid realization map"]
theorem ofMap_base {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).base = f := sorry

/-- The displayed component of the constructed total stupid map is the supplied map. -/
@[simp, stacks 0FLK "displayed computation for a total stupid realization map"]
theorem ofMap_displayed {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).displayed = m := sorry

/-- Construction of total stupid maps preserves identities. -/
@[simp, stacks 0FLK "identity computation for total stupid realization maps"]
theorem ofMap_id {K : CochainComplex A ℤ} (S : Realization F K) :
    ofMap F (Realization.Map.id F S) = 𝟙 (of F S) := sorry

/-- Construction of total stupid maps preserves composition. -/
@[simp, stacks 0FLK "composition computation for total stupid realization maps"]
theorem ofMap_comp {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    ofMap F (Realization.Map.comp F m n) = ofMap F m ≫ ofMap F n := sorry

/-- Reindexing a stupid realization map leaves the constructed total morphism unchanged. -/
@[stacks 0FLK "reindexing computation for total stupid realization maps"]
theorem ofMap_reindex {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    ofMap F (Realization.Map.reindex F h m) = ofMap F m := sorry

end Hom

/-- The stupid-to-generic functor sends a constructed total object to the total object of its
underlying generic realization. -/
@[simp, stacks 0FLK "generic image of a constructed total stupid realization"]
theorem genericFunctor_obj_of {K : CochainComplex A ℤ} (S : Realization F K) :
    (genericFunctor F).obj (of F S) =
      RightDerived.SpectralSequence.Realization.Total.of F S.original := sorry

/-- The stupid-to-generic functor sends a constructed total map to the total map of its
underlying generic realization map. -/
@[simp, stacks 0FLK "generic image of a constructed total stupid realization map"]
theorem genericFunctor_map_ofMap {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (genericFunctor F).map (Hom.ofMap F m) =
      RightDerived.SpectralSequence.Realization.Total.Hom.ofMap F m.original := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
