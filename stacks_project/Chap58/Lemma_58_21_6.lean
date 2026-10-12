/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Purity
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.21.6: if purity holds at every stalk outside an open immersion of
Noetherian schemes, restriction of finite étale covers is essentially surjective. -/
@[stacks 0EY7] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChangeEssSurjOfPurity :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X)
      [IsNoetherian U] [IsNoetherian X] [IsOpenImmersion j],
      (∀ x : X, x ∉ Set.range j.base →
        AlgebraicGeometry.PuncturedSpectrum.HasPurity (X.presheaf.stalk x)) →
        (AlgebraicGeometry.Scheme.finiteEtaleBaseChange j).EssSurj)

end AlgebraicGeometry.Scheme
