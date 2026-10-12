/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration

/-!
# Compatibility checks for ideal filtrations
-/

@[expose] public section

open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- The filtration infrastructure is owned by the formal-deformation library. -/
#check (CompleteLocalAlgCat.AdicIdealFiltration :
  CompleteLocalAlgCat Λ k → Type u)

#check (CompleteLocalAlgCat.AdicIdealFiltration.maximalAdic :
  ∀ (R : CompleteLocalAlgCat Λ k), CompleteLocalAlgCat.AdicIdealFiltration R)

#check (CompleteLocalAlgCat.AdicIdealFiltration.truncationComparison :
  ∀ {R : CompleteLocalAlgCat Λ k}
    (I : CompleteLocalAlgCat.AdicIdealFiltration R) (n : ℕ),
    I.truncation (I.stageIndex n) ⟶ R.truncation n)
