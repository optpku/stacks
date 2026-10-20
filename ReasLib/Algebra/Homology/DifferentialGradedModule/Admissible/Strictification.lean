module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Strictifying Homotopy-Commutative Squares of DG Modules

An admissibly monic top map lets one alter the right side of a homotopy-commutative square to
make it commute strictly.  Dually, an admissibly epic bottom map lets one alter the left side.
The construction-facing statements take the chosen homotopy explicitly; choice-free companions
consume only its existence.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L M N : DifferentialGradedModule.{u, w} A}

/-- Lemma 22.7.3 (1) (09JV): if the top map of a homotopy-commutative square is admissibly
monic, the right map can be replaced by a homotopic map making the square commute strictly. -/
@[stacks 09JV]
theorem exists_homotopic_rightMap_of_admissibleMono
    (f : K ⟶ L) (a : K ⟶ M) (g : M ⟶ N) (b : L ⟶ N)
    (comm : Homotopy (f ≫ b) (a ≫ g)) (hf : IsAdmissibleMono f) :
    ∃ b' : L ⟶ N, Nonempty (Homotopy b b') ∧ f ≫ b' = a ≫ g := sorry

/-- A choice-free homotopy-commutative square admits the same strictification on the right. -/
theorem exists_homotopic_rightMap_of_admissibleMono_of_nonempty
    (f : K ⟶ L) (a : K ⟶ M) (g : M ⟶ N) (b : L ⟶ N)
    (comm : Nonempty (Homotopy (f ≫ b) (a ≫ g))) (hf : IsAdmissibleMono f) :
    ∃ b' : L ⟶ N, Nonempty (Homotopy b b') ∧ f ≫ b' = a ≫ g := sorry

/-- Lemma 22.7.3 (2) (09JV): if the bottom map of a homotopy-commutative square is admissibly
epic, the left map can be replaced by a homotopic map making the square commute strictly. -/
@[stacks 09JV]
theorem exists_homotopic_leftMap_of_admissibleEpi
    (f : K ⟶ L) (a : K ⟶ M) (g : M ⟶ N) (b : L ⟶ N)
    (comm : Homotopy (f ≫ b) (a ≫ g)) (hg : IsAdmissibleEpi g) :
    ∃ a' : K ⟶ M, Nonempty (Homotopy a a') ∧ f ≫ b = a' ≫ g := sorry

/-- A choice-free homotopy-commutative square admits the same strictification on the left. -/
theorem exists_homotopic_leftMap_of_admissibleEpi_of_nonempty
    (f : K ⟶ L) (a : K ⟶ M) (g : M ⟶ N) (b : L ⟶ N)
    (comm : Nonempty (Homotopy (f ≫ b) (a ≫ g))) (hg : IsAdmissibleEpi g) :
    ∃ a' : K ⟶ M, Nonempty (Homotopy a a') ∧ f ≫ b = a' ≫ g := sorry

end DifferentialGradedModule
