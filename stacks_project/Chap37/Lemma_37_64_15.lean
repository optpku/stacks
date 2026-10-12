/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.WeaklyEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.64.15: if `f : U ⟶ X` is weakly étale and `X` has prime characteristic
`p`, then the relative Frobenius `U ⟶ Scheme.Hom.relativeFrobeniusTarget f` is an
isomorphism. -/
@[stacks 0F6W] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isIso :
    ∀ {p : ℕ} [Fact p.Prime] {U X : Scheme.{u}} (f : U ⟶ X)
      [Scheme.IsCharP X p] [WeaklyEtale f],
      IsIso (Scheme.Hom.relativeFrobenius (p := p) f))
