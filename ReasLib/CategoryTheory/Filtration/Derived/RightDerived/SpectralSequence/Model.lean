/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Filtration.Complex.KInjective.Functoriality
public import ReasLib.CategoryTheory.Filtration.Map.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered models for unbounded right-derived functors

This file defines the filtered model attached to an explicit filtered K-injective resolution and the maps induced by resolution morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

/-- Applying a monomorphism-preserving additive functor degreewise to filtered complexes. -/
@[stacks 0BKK "functor on filtered complexes underlying the right-derived model"]
noncomputable abbrev filteredFunctor : FilteredComplex A ⥤ FilteredComplex B :=
  (FilteredObject.mapFunctor F).mapHomologicalComplex (up ℤ)

/-- Applying an additive functor degreewise to an explicit filtered K-injective resolution gives
the filtered model for its right-derived spectral sequence. -/
@[stacks 0BKK "filtered right-derived model"]
noncomputable abbrev model {K : FilteredComplex A}
    (R : KInjectiveResolution K) : FilteredComplex B :=
  (filteredFunctor F).obj R.complex

/-- The morphism of filtered right-derived models induced by a morphism of explicit resolutions. -/
@[stacks 0BKK "morphism of filtered right-derived models"]
noncomputable abbrev modelMap {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (m : KInjectiveResolution.Map f R S) : model F R ⟶ model F S :=
  (filteredFunctor F).map m.hom

/-- The model map induced by the identity resolution map is the identity. -/
@[simp, stacks 0BKK "identity morphism of filtered right-derived models"]
theorem modelMap_id {K : FilteredComplex A} (R : KInjectiveResolution K) :
    modelMap F (KInjectiveResolution.Map.id R) = 𝟙 (model F R) := sorry

/-- The model map induced by a composite resolution map is the composite model map. -/
@[simp, stacks 0BKK "composition of morphisms of filtered right-derived models"]
theorem modelMap_comp {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (m : KInjectiveResolution.Map f R S)
    (n : KInjectiveResolution.Map g S T) :
    modelMap F (KInjectiveResolution.Map.comp m n) = modelMap F m ≫ modelMap F n := sorry

/-- Reindexing a resolution map does not change the induced morphism of filtered models. -/
@[simp, stacks 0BKK "reindexing morphisms of filtered right-derived models"]
theorem modelMap_reindex {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : KInjectiveResolution.Map f R S) :
    modelMap F (KInjectiveResolution.Map.reindex h m) = modelMap F m := sorry

end CategoryTheory.FilteredComplex.RightDerived

