/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 41.14.3: if `f : U ⟶ X` is étale and `X` has prime characteristic `p`,
then the relative Frobenius `U ⟶ Scheme.Hom.relativeFrobeniusTarget f` is an
isomorphism. -/
@[stacks 0EBS] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isIso_of_etale :
    {p : ℕ} → [Fact p.Prime] → {U X : Scheme.{u}} → (f : U ⟶ X) →
      [Scheme.IsCharP X p] → [Etale f] →
        IsIso (Scheme.Hom.relativeFrobenius (p := p) f))
