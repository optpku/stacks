/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution

/-!
# Bounded Targets of Strict Filtered-Injective Resolutions

This leaf exposes the bounded-below target and comparison carried by a strict
filtered-injective resolution.  Maps retain both their bounded-complex presentation and their
presentation in the termwise filtered-injective full subcategory.  All data are obtained directly
from the stored resolution and map fields; no choice of resolutions or comparison maps is made.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The resolving complex, viewed as a bounded-below complex of finite filtered objects. -/
@[stacks 05TW "bounded target of a strict filtered-injective resolution"]
abbrev target {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : CochainComplex.Plus (FilteredObject.Finite.category C) :=
  R.complex.obj

/-- The comparison from a bounded-below complex to the bounded target of its chosen strict
filtered-injective resolution. -/
@[stacks 05TW "bounded comparison of a strict filtered-injective resolution"]
def comparison {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : K ⟶ R.target :=
  ObjectProperty.homMk R.ι

/-- Forgetting the bounded presentation of the resolution comparison recovers its stored
cochain map. -/
@[simp, stacks 05TW "bounded comparison of a strict filtered-injective resolution"]
theorem comparison_hom {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : R.comparison.hom = R.ι := rfl

namespace Map

/-- The morphism between the bounded targets carried by a map of strict filtered-injective
resolutions. -/
@[stacks 05TU "bounded target map of strict filtered-injective resolutions"]
def targetMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) : R.target ⟶ S.target :=
  ObjectProperty.homMk m.hom

/-- A map of strict filtered-injective resolutions, retaining the termwise filtered-injective
full-subcategory presentation of its source and target. -/
@[stacks 05TU "termwise filtered-injective target map"]
def complexMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) : R.complex ⟶ S.complex :=
  ObjectProperty.homMk m.targetMap

/-- Forgetting a bounded target map recovers the cochain map stored by the resolution map. -/
@[simp, stacks 05TU "bounded target map of strict filtered-injective resolutions"]
theorem targetMap_hom
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    m.targetMap.hom = m.hom := rfl

/-- Forgetting the termwise filtered-injective presentation of a target map recovers its
bounded-complex presentation. -/
@[simp, stacks 05TU "termwise filtered-injective target map"]
theorem complexMap_hom
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    m.complexMap.hom = m.targetMap := rfl

/-- The bounded target map is compatible with the source morphism and the two resolution
comparisons. -/
@[reassoc, stacks 05TU "naturality of bounded strict-resolution comparisons"]
theorem comparison_naturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    R.comparison ≫ m.targetMap = f ≫ S.comparison := by
  apply ObjectProperty.hom_ext
  exact m.ι_naturality

/-- The bounded target map of the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity bounded target map"]
theorem id_targetMap {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : (id R).targetMap = 𝟙 R.target := rfl

/-- Bounded target maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of bounded target maps"]
theorem comp_targetMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).targetMap = m.targetMap ≫ n.targetMap := rfl

/-- Reindexing a resolution map does not change its bounded target map. -/
@[simp, stacks 05TU "reindexing a bounded target map"]
theorem reindex_targetMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).targetMap = m.targetMap := rfl

/-- The termwise filtered-injective target map of the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity termwise filtered-injective target map"]
theorem id_complexMap {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : (id R).complexMap = 𝟙 R.complex := rfl

/-- Termwise filtered-injective target maps preserve composition of resolution maps. -/
@[simp, stacks 05TU "composition of termwise filtered-injective target maps"]
theorem comp_complexMap
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).complexMap = m.complexMap ≫ n.complexMap := rfl

/-- Reindexing a resolution map does not change its termwise filtered-injective target map. -/
@[simp, stacks 05TU "reindexing a termwise filtered-injective target map"]
theorem reindex_complexMap
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).complexMap = m.complexMap := rfl

end Map

end CochainComplex.FilteredInjectivePlus.Resolution
