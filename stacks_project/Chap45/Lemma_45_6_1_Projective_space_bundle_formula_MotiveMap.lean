/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.ProjectiveBundle

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

#check (ChowMotive.ProjectiveBundle.formulaMap :
  ∀ {k : Type u} [Field k] (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E],
    (⨁ fun i : Fin r ↦ ChowMotive.tateTwist X.scheme (-(i : ℤ))) ⟶
      ChowMotive.h P.scheme)
