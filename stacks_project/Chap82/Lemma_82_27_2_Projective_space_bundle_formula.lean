/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

/- Lemma 82.27.2 (Projective space bundle formula) -/
@[stacks 0ERV] #check
  (HigherChern.formula_bijective :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) [E.IsQuasicoherent] (q : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (k : ℤ),
      Function.Bijective
        (ProjectiveFormulaMap.formula f δ (ProjectiveAtlas.projection E) q
          (TautologicalDescent.O1 E) k))
