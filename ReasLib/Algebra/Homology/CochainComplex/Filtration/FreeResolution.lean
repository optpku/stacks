module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free K-Flat Resolutions of Filtered Complexes

Every filtered cochain complex of modules admits a filtered resolution that is termwise free and
K-flat on the underlying complex, every filtration stage, and every graded piece.

@stack 0H7X
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace CategoryTheory.FilteredComplex

variable {R : Type u} [CommRing R]

/-- Lemma 15.64.2: a filtered cochain complex admits a termwise-free K-flat resolution which is a
quasi-isomorphism on the underlying complex, every filtration stage, and every graded piece. -/
@[stacks 0H7X "free K-flat resolution of a filtered complex"]
theorem exists_freeKFlatResolution (K : FilteredCochainComplex (ModuleCat R)) :
    ∃ (P : FilteredCochainComplex (ModuleCat R)) (f : P ⟶ K),
      P.underlying.IsTermwiseFree ∧
        (∀ p : ℤ, (P.stage p).IsTermwiseFree) ∧
        (∀ p : ℤ, (P.gradedPiece p).IsTermwiseFree) ∧
        P.underlying.IsKFlat ∧
        (∀ p : ℤ, (P.stage p).IsKFlat) ∧
        (∀ p : ℤ, (P.gradedPiece p).IsKFlat) ∧
        QuasiIso (P.underlyingMap f) ∧
        (∀ p : ℤ, QuasiIso (P.stageMap f p)) ∧
        ∀ p : ℤ, QuasiIso (P.gradedPieceMap f p) := sorry

end CategoryTheory.FilteredComplex
