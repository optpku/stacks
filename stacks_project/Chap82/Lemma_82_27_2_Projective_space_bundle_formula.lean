module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

universe u

/- Lemma 82.27.2 (Projective space bundle formula) -/
@[stacks 0ERV] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern.formulaMap_bijective :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      (k : ℤ),
      Function.Bijective
        (HigherChern.formulaMap f δ E r k))
