/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Factorization
public import ReasLib.CategoryTheory.ComposableArrows.Property

/-!
# Finite Admissibly Monic Homotopy Replacements

Every finite row of differential graded modules has a comparison row whose successor maps are
admissible monomorphisms and whose comparison components are homotopy equivalences.  The public
statement uses reusable morphism-property views, with a pointwise bridge for callers working
directly with the canonical `Fin` indices.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule
namespace HomotopyReplacement

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Lemma 22.7.5 (09JX): every finite composable row of DG-modules admits a comparison row with
admissibly monic successor maps and componentwise homotopy equivalences. -/
@[stacks 09JX]
theorem exists_admissibleMono {n : ℕ}
    (S : ComposableArrows (DifferentialGradedModule.{u, w} A) n) :
    ∃ (T : ComposableArrows (DifferentialGradedModule.{u, w} A) n) (phi : T ⟶ S),
      ComposableArrows.arrowProperty (admissibleMonomorphisms A) T ∧
        ComposableArrows.componentProperty (homotopyEquivalences A) phi := sorry

/-- Pointwise form of the finite admissibly monic homotopy replacement theorem. -/
theorem exists_admissibleMono_pointwise {n : ℕ}
    (S : ComposableArrows (DifferentialGradedModule.{u, w} A) n) :
    ∃ (T : ComposableArrows (DifferentialGradedModule.{u, w} A) n) (phi : T ⟶ S),
      (∀ i : Fin n, IsAdmissibleMono (T.map' i.1 (i.1 + 1))) ∧
        (∀ i : Fin (n + 1), homotopyEquivalences A (phi.app i)) := sorry

end HomotopyReplacement
end DifferentialGradedModule
