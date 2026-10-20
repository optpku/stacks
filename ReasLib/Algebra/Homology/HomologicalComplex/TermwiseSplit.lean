/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Termwise split morphisms of homological complexes

Termwise split monomorphisms and epimorphisms are canonical morphism properties of homological
complexes, independent of the indexing shape.  Naming them as `MorphismProperty`s lets finite
diagrams, localization arguments, and admissibility bridges share one interface.
-/

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} (c : ComplexShape ι)

/-- The morphism property of being split monic in every degree. -/
@[stacks 014M "termwise split-monomorphism property"]
def termwiseSplitMono : MorphismProperty (HomologicalComplex C c) :=
  fun _ _ f ↦ ∀ i : ι, IsSplitMono (f.f i)

/-- The morphism property of being split epic in every degree. -/
@[stacks 014M "termwise split-epimorphism property"]
def termwiseSplitEpi : MorphismProperty (HomologicalComplex C c) :=
  fun _ _ f ↦ ∀ i : ι, IsSplitEpi (f.f i)

/-- Termwise split monomorphisms contain identities and are closed under composition. -/
instance termwiseSplitMono_isMultiplicative : (termwiseSplitMono C c).IsMultiplicative where
  id_mem := sorry
  comp_mem := sorry

/-- Termwise split epimorphisms contain identities and are closed under composition. -/
instance termwiseSplitEpi_isMultiplicative : (termwiseSplitEpi C c).IsMultiplicative where
  id_mem := sorry
  comp_mem := sorry

/-- Membership in `termwiseSplitMono` is the pointwise split-monomorphism condition. -/
@[simp]
theorem termwiseSplitMono_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    termwiseSplitMono C c f ↔ ∀ i : ι, IsSplitMono (f.f i) := sorry

/-- Membership in `termwiseSplitEpi` is the pointwise split-epimorphism condition. -/
@[simp]
theorem termwiseSplitEpi_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    termwiseSplitEpi C c f ↔ ∀ i : ι, IsSplitEpi (f.f i) := sorry

/-- A composite of termwise split monomorphisms is termwise split monic. -/
theorem termwiseSplitMono_comp {K L M : HomologicalComplex C c}
    {f : K ⟶ L} {g : L ⟶ M}
    (hf : termwiseSplitMono C c f) (hg : termwiseSplitMono C c g) :
    termwiseSplitMono C c (f ≫ g) := sorry

/-- A composite of termwise split epimorphisms is termwise split epic. -/
theorem termwiseSplitEpi_comp {K L M : HomologicalComplex C c}
    {f : K ⟶ L} {g : L ⟶ M}
    (hf : termwiseSplitEpi C c f) (hg : termwiseSplitEpi C c g) :
    termwiseSplitEpi C c (f ≫ g) := sorry

end HomologicalComplex
