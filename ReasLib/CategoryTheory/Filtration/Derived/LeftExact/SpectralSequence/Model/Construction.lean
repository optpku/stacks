module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded
public import ReasLib.CategoryTheory.Filtration.LeftExact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite filtered right-derived models

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The degreewise finite-filtered model obtained by applying a left-exact functor to a chosen
strict filtered-injective resolution. -/
@[stacks 015W "strict filtered-injective model for a filtered right-derived functor"]
noncomputable abbrev modelFunctor (T : A ⥤ₗ B) :
    _root_.CochainComplex (FilteredObject.Finite.category A) ℤ ⥤ FilteredComplex B :=
  (FilteredObject.Finite.mapFunctor T.obj).mapHomologicalComplex (up ℤ) ⋙
    FilteredObject.Finite.CochainComplex.inclusion B

/-- The filtered model attached to a chosen strict filtered-injective resolution. -/
@[stacks 015W "strict filtered-injective model for a filtered right-derived functor"]
noncomputable abbrev model (T : A ⥤ₗ B)
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (R : Resolution K) :
    FilteredComplex B :=
  (modelFunctor T).obj ((_root_.CochainComplex.FilteredInjectivePlus.ι A).obj R.complex)

/-- The filtered-model morphism induced by a morphism of strict filtered-injective
resolutions. -/
@[stacks 015W "morphism of strict filtered-injective right-derived models"]
noncomputable abbrev modelMap (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    model T R ⟶ model T S :=
  (modelFunctor T).map m.hom

/-- The model map induced by the identity resolution map is the identity. -/
@[simp, stacks 015W "identity morphism of strict filtered-injective right-derived models"]
theorem modelMap_id (T : A ⥤ₗ B)
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (R : Resolution K) :
    modelMap T (Resolution.Map.id R) = 𝟙 (model T R) := sorry

/-- The model map induced by a composite resolution map is the composite model map. -/
@[simp, stacks 015W "composition of strict filtered-injective right-derived model maps"]
theorem modelMap_comp (T : A ⥤ₗ B)
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {U : Resolution M} (m : Resolution.Map f R S) (n : Resolution.Map g S U) :
    modelMap T (Resolution.Map.comp m n) = modelMap T m ≫ modelMap T n := sorry

/-- Reindexing a resolution map does not change its induced filtered-model morphism. -/
@[simp, stacks 015W "reindexing strict filtered-injective right-derived model maps"]
theorem modelMap_reindex (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Resolution.Map f R S) :
    modelMap T (Resolution.Map.reindex h m) = modelMap T m := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
