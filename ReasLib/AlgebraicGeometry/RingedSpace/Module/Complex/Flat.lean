module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise-flat complexes on ringed spaces

The canonical owner of termwise flatness is the monoidal-category predicate
`HomologicalComplex.IsTermwiseFlat`.  This file supplies the ringed-space view in terms of
stalkwise-flat module sheaves, without introducing a second class or a ringed-space alias of
the predicate.  Use `(isTermwiseFlat_iff K).mpr` to build termwise flatness from stalkwise
flat terms.
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

end AlgebraicGeometry.RingedSpace.CochainComplex
