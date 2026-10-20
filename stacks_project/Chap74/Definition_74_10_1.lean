/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Category
public import ReasLib.CategoryTheory.MorphismProperty.SiteLocal
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

variable (S : AlgebraicGeometry.Scheme.{u})

/- Definition 74.10.1: for a scheme `S`, a property `P` of morphisms of algebraic
spaces over `S`, and a precoverage `K` equal to one of the fpqc, fppf, syntomic,
smooth, or étale precoverages on the canonical category `AlgebraicSpace.Cat S`
induced by functors of points, we say `P` is τ-local on the base, or τ-local on
the target, or local on the base for the τ-topology, if for every `K`-cover `𝒰`
and morphism `f : X ⟶ Y` of algebraic spaces over `S`, `P f ↔ ∀ i,
P (pullback.snd f (𝒰.f i))`. -/
@[stacks 03YH] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_forall_zeroHypercover :
    ∀ (P : CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace.Cat S))
      (K : CategoryTheory.Precoverage (AlgebraicGeometry.AlgebraicSpace.Cat S))
      [K.HasPullbacks] [P.RespectsIso],
      P.IsLocalAtTarget K ↔
        ∀ ⦃X Y : AlgebraicGeometry.AlgebraicSpace.Cat S⦄ (f : X ⟶ Y)
          (𝒰 : CategoryTheory.Precoverage.ZeroHypercover K Y),
          P f ↔ ∀ i, P (CategoryTheory.Limits.pullback.snd f (𝒰.f i)))
