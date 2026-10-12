/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Monoidal

@[expose] public section

universe uR uM

/- Finitely presented modules inherit the tensor-product monoidal structure. -/
#check (ModuleCat.isFinitePresentation.instIsMonoidal :
  ∀ (R : Type uR) [CommRing R],
    (ModuleCat.isFinitePresentation.{uR, max uR uM} R).IsMonoidal)
