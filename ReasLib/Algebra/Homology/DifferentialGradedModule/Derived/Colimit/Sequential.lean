/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.DeltaFunctor.Limits
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.SequentialColimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential Colimits in a DG-Module Derived Category

The generic delta-functor sequential-colimit API specializes to the canonical functor from right
differential graded modules to their derived category.  The generic owner supplies the telescope
cocone, boundary map, distinguished triangle, and presentation; this leaf records only the
source-facing specialization.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped DifferentialGradedModule

variable {R : Type u} [CommRing R]

namespace DifferentialGradedModule.Derived.SequentialColimit

variable {A : CochainDGAlgebra.{u, v} R}
variable (S : ℕ ⥤ DifferentialGradedModule.{u, v} A)

/-- Lemma 22.23.2 (0CRL): the derived image of the termwise colimit is a homotopy colimit of a
sequential diagram of right DG modules. -/
@[stacks 0CRL "sequential colimit as a homotopy colimit of DG modules"]
theorem isOf :
    HomotopyColimit.IsOf (S ⋙ fromModules A) ((fromModules A).obj (colimit S)) := sorry

end DifferentialGradedModule.Derived.SequentialColimit
