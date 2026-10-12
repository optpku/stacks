/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.MorphismProperty.SiteLocal
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Definition 35.26.1: For any of the Zariski, fpqc, fppf, étale, smooth, or syntomic
precoverages, a property of morphisms of schemes is local on the source if and only if it
holds for a morphism exactly when it holds after precomposition with every member of each
covering family of its source. -/
@[stacks 036G] #check
  (CategoryTheory.MorphismProperty.IsLocalAtSource.iff_forall_zeroHypercover :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      (K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}) [P.RespectsIso],
      P.IsLocalAtSource K ↔
        ∀ ⦃X Y : AlgebraicGeometry.Scheme.{u}⦄ (f : X ⟶ Y)
          (𝒰 : CategoryTheory.Precoverage.ZeroHypercover K X),
          P f ↔ ∀ i, P (𝒰.f i ≫ f))
