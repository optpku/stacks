/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SmoothCurve
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 44.3.1 (1): a finite locally free closed subscheme of a smooth relative curve is a
relative effective Cartier divisor. -/
@[stacks 0B9D] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.of_isFiniteLocallyFree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      (D : X.IdealSheafData),
      IsFiniteLocallyFree (D.subschemeι ≫ f) → IsRelativeEffectiveCartierDivisor f D)

/- Lemma 44.3.1 (2): on a smooth relative curve, a closed subscheme is a relative effective
Cartier divisor exactly when its structure morphism is locally quasi-finite, flat, and locally
of finite presentation. -/
@[stacks 0B9D] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.iff_locallyQuasiFinite_flat_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      (D : X.IdealSheafData),
      IsRelativeEffectiveCartierDivisor f D ↔
        LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
          LocallyOfFinitePresentation (D.subschemeι ≫ f))

/- Lemma 44.3.1 (3): local quasi-finiteness, flatness, and local finite presentation imply
local finite type, local quasi-finiteness, and flatness. -/
@[stacks 0B9D] #check
  (AlgebraicGeometry.locallyQuasiFinite_flat_of_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      (D : X.IdealSheafData),
      LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
          LocallyOfFinitePresentation (D.subschemeι ≫ f) →
        LocallyOfFiniteType (D.subschemeι ≫ f) ∧ LocallyQuasiFinite (D.subschemeι ≫ f) ∧
          Flat (D.subschemeι ≫ f))

/- Lemma 44.3.1 (4): over a locally Noetherian base, local finite type, local quasi-finiteness,
and flatness are equivalent to local quasi-finiteness, flatness, and local finite presentation. -/
@[stacks 0B9D] #check
  (AlgebraicGeometry.LocallyQuasiFinite.flat_iff_flat_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      [IsLocallyNoetherian S] (D : X.IdealSheafData),
      (LocallyOfFiniteType (D.subschemeι ≫ f) ∧ LocallyQuasiFinite (D.subschemeι ≫ f) ∧
        Flat (D.subschemeι ≫ f)) ↔
        LocallyQuasiFinite (D.subschemeι ≫ f) ∧ Flat (D.subschemeι ≫ f) ∧
          LocallyOfFinitePresentation (D.subschemeι ≫ f))

/- Lemma 44.3.1 (5): when the smooth relative curve is proper over the base, its finite locally
free closed subschemes are exactly its relative effective Cartier divisors. -/
@[stacks 0B9D] #check
  (AlgebraicGeometry.isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [IsProper f]
      (D : X.IdealSheafData),
      IsFiniteLocallyFree (D.subschemeι ≫ f) ↔ IsRelativeEffectiveCartierDivisor f D)

end AlgebraicGeometry
