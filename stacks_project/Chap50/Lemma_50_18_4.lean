/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

open PerfectDerived.TorNegOneZero.Determinant
open Scheme.Hom.NaiveCotangent.BaseChange

/- Lemma 50.18.4: uniqueness of determinant-twisted differential-form comparison families after an open pullback. -/
@[stacks 0H9G] #check (AlgebraicGeometry.Scheme.RelativeDifferentials.comparisonFamily_unique :
  ∀ {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a)
    [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (P : Pullback b)
    (c : ∀ p : ℕ,
      (Λ[p] (Ω[(terminal.from Y).toShHom])) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          P.source.line (naiveCotangentObject f))
    (hcOne : MapsUnitToDiscriminant f P.source c)
    (hcWedge : CompatibleWithWedge f P.source c)
    (c₁ c₂ : ∀ p : ℕ,
      (Λ[p] (Ω[(terminal.from Y').toShHom])) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          P.target.line (baseChangedNaiveCotangentObject b f' f a sq))
    (hc₁one : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target c₁)
    (hc₁wedge : BaseChangedCompatibleWithWedge b f' f a sq P.target c₁)
    (hc₂one : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target c₂)
    (hc₂wedge : BaseChangedCompatibleWithWedge b f' f a sq P.target c₂)
    (hc₁baseChange : ∀ p : ℕ,
      (Scheme.Modules.pullback b).map (c p) ≫
          comparisonTargetMap b f' f a sq P p =
        absoluteFormComparison b p ≫ c₁ p)
    (hc₂baseChange : ∀ p : ℕ,
      (Scheme.Modules.pullback b).map (c p) ≫
          comparisonTargetMap b f' f a sq P p =
        absoluteFormComparison b p ≫ c₂ p),
    c₁ = c₂)

end AlgebraicGeometry.Scheme.RelativeDifferentials
