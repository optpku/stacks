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

/- Definition 35.22.1: for a property `P` of scheme morphisms and a precoverage
`K` equal to `Scheme.fpqcPrecoverage`, `Scheme.fppfPrecoverage`,
`Scheme.bigSyntomicPrecoverage`, `Scheme.bigSmoothPrecoverage`,
`Scheme.etalePrecoverage`, or `Scheme.zariskiPrecoverage`, being local on the
target means that for every `K`-cover `𝒰` and morphism `f : X ⟶ Y`,
`P f ↔ ∀ i, P (pullback.snd f (𝒰.f i))`. -/
@[stacks 02KO] #check
  (CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_forall_zeroHypercover :
    ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      (K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u})
      [K.HasPullbacks] [P.RespectsIso],
      P.IsLocalAtTarget K ↔
        ∀ ⦃X Y : AlgebraicGeometry.Scheme.{u}⦄ (f : X ⟶ Y)
          (𝒰 : CategoryTheory.Precoverage.ZeroHypercover K Y),
          P f ↔ ∀ i, P (CategoryTheory.Limits.pullback.snd f (𝒰.f i)))
