/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FormalFunctions
import StacksCheckRecall

/-!
# Spell-out of the theorem on formal functions

If the Noetherian base ring `A` is `I`-adically complete, the comparison
`H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is already an isomorphism, so
completion on the left-hand side is unnecessary.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits Opposite

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.6: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)`
is a proper morphism of algebraic spaces, and `F` is coherent on `X`, then the
canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` is an isomorphism of
`A`-modules for every `p : ℕ`. -/
@[stacks 08B0] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.isIso_toLimit :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules] (p : ℕ),
      IsIso (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toLimit I f F p))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toLimit :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules] (p : ℕ),
      GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
        limit (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem
          I f F p))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toLimit_comp_π :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules] (p n : ℕ),
      AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toLimit I f F p ≫
          limit.π
            (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem
              I f F p) (op n) =
        AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toQuotientCohomology
          I f F p n)

