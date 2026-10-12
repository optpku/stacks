/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.LocallyQuasiFiniteRefinement

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.FppfCover

/- Lemma 37.23.6: every fppf cover of a scheme admits an fppf refinement whose
component morphisms are locally quasi-finite. -/
@[stacks 0572] #check
  (AlgebraicGeometry.FppfCover.exists_locallyQuasiFiniteRefinement :
    {S : Scheme.{u}} → (𝒰 : FppfCover.{u, v} S) →
    ∃ (𝒱 : FppfCover.{u, max u v} S)
      (φ : Precoverage.ZeroHypercover.Hom
        Scheme.fppfPrecoverage 𝒱 𝒰),
      ∀ j : 𝒱.I₀, LocallyQuasiFinite (𝒱.f j))

end AlgebraicGeometry.FppfCover
