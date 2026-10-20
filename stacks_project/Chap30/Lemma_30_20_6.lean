/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FormalFunctions
import StacksCheckRecall

/-!
# Spell-out of the theorem on formal functions

If the Noetherian base ring `A` is `I`-adically complete, the comparison
`H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is already an isomorphism, so
completion on the left-hand side is unnecessary.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

/- Lemma 30.20.6: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)`
is a proper morphism, and `F` is a coherent sheaf on `X`, then the canonical
comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is an isomorphism of
`A`-modules for every `p : ℕ`. -/
@[stacks 087U] #check
  (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.isIso_toLimit :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    IsIso (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.toLimit I f F p))
