/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter.Dual

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.45.4: The degree-`i` Chern-character component of the dual of a finite
locally free module `E` is `(-1) ^ i` times the corresponding component of `E` in
`Aⁱ(X) ⊗[ℤ] ℚ`. -/
@[stacks 0FAB] #check
  (AlgebraicGeometry.ChernClass.Theory.characterComponent_dual :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      AlgebraicGeometry.ChernClass.Theory.characterComponent δ p classes
          (Scheme.Modules.dual E) i =
        ((-1 : ℤ) ^ i) •
          AlgebraicGeometry.ChernClass.Theory.characterComponent δ p classes E i)
