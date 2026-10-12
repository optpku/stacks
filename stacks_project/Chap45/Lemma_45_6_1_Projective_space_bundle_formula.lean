/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.ProjectiveBundle
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 45.6.1 (Projective space bundle formula): in the situation of a represented
projective bundle of a finite locally free rank-`r` module, the morphism
`∑ c_i : ⨁_{i=0}^{r-1} h(X)(-i) ⟶ h(P)` is an isomorphism in the category of motives. -/
@[stacks 0FGQ] #check (ChowMotive.ProjectiveBundle.formulaMap_isIso :
  ∀ {k : Type u} [Field k] (X P : AlgebraicGeometry.Correspondence.Category k)
    (E : AlgebraicGeometry.Scheme.Modules X.scheme.left) (r : ℕ)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (p : P.scheme ⟶ X.scheme)
    (hp : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation p.left E),
    CategoryTheory.IsIso
      (ChowMotive.ProjectiveBundle.formulaMap X P E p hp r))
