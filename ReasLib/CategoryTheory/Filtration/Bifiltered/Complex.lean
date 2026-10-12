/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.CategoryTheory.Filtration.Bifiltered.ZeroMorphisms
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

@[expose] public section

/-!
# Bifiltered cochain complexes

A bifiltered cochain complex is a cochain complex in bifiltered objects. The two functors to
filtered complexes retain one filtration at a time and share the same underlying cochain complex.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [HasZeroMorphisms A]

/-- A cochain complex whose terms carry two filtrations preserved by every differential. -/
@[stacks 0ESK "bifiltered complex"]
abbrev BifilteredComplex := CochainComplex (BifilteredObject A) ℤ

namespace BifilteredComplex

variable {A}

/-- Retain the first filtration of a bifiltered cochain complex. -/
@[stacks 0ESK "first filtered-complex functor"]
abbrev firstFunctor : BifilteredComplex A ⥤ FilteredComplex A :=
  (BifilteredObject.first (C := A)).mapHomologicalComplex (up ℤ)

/-- Retain the second filtration of a bifiltered cochain complex. -/
@[stacks 0ESK "second filtered-complex functor"]
abbrev secondFunctor : BifilteredComplex A ⥤ FilteredComplex A :=
  (BifilteredObject.second (C := A)).mapHomologicalComplex (up ℤ)

/-- Forget both filtrations of a bifiltered cochain complex. -/
abbrev underlyingFunctor : BifilteredComplex A ⥤ CochainComplex A ℤ :=
  (BifilteredObject.forget (C := A)).mapHomologicalComplex (up ℤ)

/-- Exchange the two filtrations of a bifiltered cochain complex. -/
abbrev swapFunctor : BifilteredComplex A ⥤ BifilteredComplex A :=
  (BifilteredObject.swap (C := A)).mapHomologicalComplex (up ℤ)

/-- The first filtered-complex view. -/
abbrev first (K : BifilteredComplex A) : FilteredComplex A :=
  firstFunctor.obj K

/-- The second filtered-complex view. -/
abbrev second (K : BifilteredComplex A) : FilteredComplex A :=
  secondFunctor.obj K

/-- The common underlying cochain complex. -/
abbrev underlying (K : BifilteredComplex A) : CochainComplex A ℤ :=
  underlyingFunctor.obj K

/-- The bifiltered complex with its two filtrations exchanged. -/
abbrev swap (K : BifilteredComplex A) : BifilteredComplex A :=
  swapFunctor.obj K

/-- The map of first filtered-complex views induced by a bifiltered-complex map. -/
abbrev firstMap {K L : BifilteredComplex A} (f : K ⟶ L) : K.first ⟶ L.first :=
  firstFunctor.map f

/-- The map of second filtered-complex views induced by a bifiltered-complex map. -/
abbrev secondMap {K L : BifilteredComplex A} (f : K ⟶ L) : K.second ⟶ L.second :=
  secondFunctor.map f

/-- The map of common underlying complexes induced by a bifiltered-complex map. -/
abbrev underlyingMap {K L : BifilteredComplex A} (f : K ⟶ L) :
    K.underlying ⟶ L.underlying :=
  underlyingFunctor.map f

/-- The inclusion of a first-filtration stage into the common underlying complex. -/
abbrev firstInclusion (K : BifilteredComplex A) (p : ℤ) :
    K.first.stage p ⟶ K.underlying :=
  K.first.stageInclusion p

/-- The inclusion of a second-filtration stage into the common underlying complex. -/
abbrev secondInclusion (K : BifilteredComplex A) (p : ℤ) :
    K.second.stage p ⟶ K.underlying :=
  K.second.stageInclusion p

/-- The first filtered view has the common underlying cochain complex. -/
@[simp]
theorem first_underlying (K : BifilteredComplex A) :
    K.first.underlying = K.underlying := sorry

/-- The second filtered view has the common underlying cochain complex. -/
@[simp]
theorem second_underlying (K : BifilteredComplex A) :
    K.second.underlying = K.underlying := sorry

/-- Swapping a bifiltered complex exchanges its first and second filtered views. -/
@[simp]
theorem swap_first (K : BifilteredComplex A) : K.swap.first = K.second := sorry

/-- Swapping a bifiltered complex exchanges its second and first filtered views. -/
@[simp]
theorem swap_second (K : BifilteredComplex A) : K.swap.second = K.first := sorry

/-- Swapping filtrations leaves the common underlying cochain complex unchanged. -/
@[simp]
theorem swap_underlying (K : BifilteredComplex A) :
    K.swap.underlying = K.underlying := sorry

end BifilteredComplex

end CategoryTheory
