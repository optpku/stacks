/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Functor
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of spectral-sequence renumbering

The standard page and bidegree renumbering is additive.  The instance is isolated from the
renumbering construction so clients that only need additive transport do not inherit unrelated
boundedness or convergence declarations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical renumbering functor preserves addition of spectral-sequence maps. -/
@[stacks 0G1Y "additivity of spectral-sequence renumbering"]
noncomputable instance functor_additive :
    (functor (C := C)).Additive := sorry

end CategoryTheory.CohomologicalSpectralSequence.Renumber
