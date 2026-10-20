/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism.IsIso
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total.PageOne
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association.Total.IsIso
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.PresentedMorphism

/-!
# The Spectral Sequence of a Filtered Complex

This facade exports the reusable API for finite-page representatives, explicit presentations,
associations with filtered complexes, and the corresponding morphisms. Import a semantic leaf
when only one layer is needed.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

end FilteredComplex

end CategoryTheory
