/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Strictification
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {K L M N : DifferentialGradedModule.{u, w} A}
variable (f : K ⟶ L) (a : K ⟶ M) (g : M ⟶ N) (b : L ⟶ N)
variable (comm : Homotopy (f ≫ b) (a ≫ g))

/- Lemma 22.7.3 (1) (09JV): an admissibly monic top map lets one replace the right map
within its homotopy class so that the square commutes strictly. -/
@[stacks 09JV] #check
  (exists_homotopic_rightMap_of_admissibleMono f a g b comm :
    IsAdmissibleMono f →
      ∃ b' : L ⟶ N, Nonempty (Homotopy b b') ∧ f ≫ b' = a ≫ g)

/- Lemma 22.7.3 (2) (09JV): dually, an admissibly epic bottom map lets one replace the
left map within its homotopy class so that the square commutes strictly. -/
@[stacks 09JV] #check
  (exists_homotopic_leftMap_of_admissibleEpi f a g b comm :
    IsAdmissibleEpi g →
      ∃ a' : K ⟶ M, Nonempty (Homotopy a a') ∧ f ≫ b = a' ≫ g)
