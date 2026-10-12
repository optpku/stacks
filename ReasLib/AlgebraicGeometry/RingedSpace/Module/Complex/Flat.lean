/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise-flat complexes on ringed spaces

The canonical owner of termwise flatness is the monoidal-category predicate
`HomologicalComplex.IsTermwiseFlat`.  This file supplies the ringed-space view in terms of
stalkwise-flat module sheaves, without introducing a second class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- For complexes of `O_X`-modules, canonical termwise flatness is equivalent to stalkwise
flatness of every term. -/
@[stacks 08CH "termwise-flat bridge"]
theorem isTermwiseFlat_iff (K : CochainComplex (Modules X) ℤ) :
    HomologicalComplex.IsTermwiseFlat K ↔
      ∀ n : ℤ, SheafOfModules.IsFlat (K.X n) := sorry

/-- Stalkwise flatness of every term constructs the canonical termwise-flat predicate. -/
theorem isTermwiseFlat_of_forall_isFlat
    (K : CochainComplex (Modules X) ℤ)
    (hK : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    HomologicalComplex.IsTermwiseFlat K := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
