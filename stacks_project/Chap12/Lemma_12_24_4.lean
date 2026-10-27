/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
import StacksCheckRecall

/-!
# Functoriality of the Associated Spectral Sequence

The reusable owner states unique existence of the spectral-sequence morphism induced by a
filtered-complex morphism. It records both the map on associated graded complexes at `E₀` and the
map induced on every explicit `Zᵣ/Bᵣ` page representative.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : FilteredComplex C}
variable {E E' : CohomologicalSpectralSequence C 0}
variable (A : FilteredComplex.Association K E) (B : FilteredComplex.Association L E')
variable (α : K ⟶ L)

/- Lemma 12.24.4 (012O): a morphism of filtered complexes induces a unique morphism between the
associated spectral sequences, compatible with their bigradings. -/
@[stacks 012O "canonical morphism of associated spectral sequences"]
#check (FilteredComplex.Association.IsCompatible.existsUnique A B α :
  ∃! φ : E ⟶ E', FilteredComplex.Association.IsCompatible A B α φ)

#check (FilteredComplex.Association.IsCompatible :
  FilteredComplex.Association K E →
    FilteredComplex.Association L E' →
      (K ⟶ L) →
        (E ⟶ E') →
          Prop)

#check (FilteredComplex.Association.Hom.pageOne_naturality :
  ∀ (φ : FilteredComplex.Association.Hom A B α) (p q : ℤ),
    (φ.hom.hom 1).f (p, q) ≫ (B.pageOneIso p q).hom =
      (A.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap (FilteredComplex.gradedPieceMap α p) (p + q))
