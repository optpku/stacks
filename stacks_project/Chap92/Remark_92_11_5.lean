/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteHomology
import StacksCheckRecall

/-!
# Spectral-sequence comparison of `𝒥/𝒥²` with the cotangent complex

Remark 92.11.5 records that the degree-two spectral-sequence differential on `C_{B/A}` is an
isomorphism, that `ker(d)` and `coker(d)` are constant on the surjective subcategory `C'_{B/A}`,
and the resulting identifications `H_n(C_{B/A}, 𝒥/𝒥²) ≅ H^{-n}(L_{B/A})` for `n ≥ 2` and
`H^{-2}(L_{B/A}) ≅ H_0(C_{B/A}, Tor_1^O(𝒥, underline{B}))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open CommAlgCat.Over.Polynomial
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

noncomputable section

universe u q q'

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/- Remark 92.11.5 (1). The degree-two spectral-sequence differential is an isomorphism. -/
@[stacks 09D5] #check (Algebra.PolynomialSite.conormalHomology_two_isIsomorphic_kernelTorHomology_zero A B :
    IsIsomorphic (lowerShriekHomology A B (conormalSheaf A B) (-2))
      (lowerShriekHomology A B (kernelTorSheaf A B 1) 0))

/- Remark 92.11.5 (2). On the surjective subcategory, the kernel is constant on
`H^{-1}(L_{B/A})`. -/
@[stacks 09D5] #check (Algebra.PolynomialSite.kernel_conormalToOmega_restrict_isIsomorphic_const A B :
    IsIsomorphic (restrictSurjective A B (kernel (conormalToOmega A B)))
      ((Functor.const _).obj ((cotangentComplex A B).homology (-1))))

/- Remark 92.11.5 (3). On the surjective subcategory, the cokernel is constant on
`H^{-2}(L_{B/A})`. -/
@[stacks 09D5] #check (Algebra.PolynomialSite.coker_conormalToOmega_restrict_isIsomorphic_const A B :
    IsIsomorphic (restrictSurjective A B (cokernel (conormalToOmega A B)))
      ((Functor.const _).obj ((cotangentComplex A B).homology (-2 : ℤ))))

/- Remark 92.11.5 (4). The kernel has vanishing higher homology. -/
@[stacks 09D5] #check (Algebra.PolynomialSite.kernel_conormalToOmega_higherHomology_isZero A B :
    ∀ {n : ℕ}, 0 < n →
      IsZero (lowerShriekHomology A B (kernel (conormalToOmega A B)) (-n : ℤ)))

/- Remark 92.11.5 (5). The cokernel has vanishing higher homology. -/
@[stacks 09D5] #check (Algebra.PolynomialSite.coker_conormalToOmega_higherHomology_isZero A B :
    ∀ {n : ℕ}, 0 < n →
      IsZero (lowerShriekHomology A B (cokernel (conormalToOmega A B)) (-n : ℤ)))

/- Remark 92.11.5 (6). For `n ≥ 2`, the conormal-to-differentials homology map is an
isomorphism. -/
@[stacks 09D5] #check (Algebra.CotangentComplex.conormalToOmega_lowerShriekHomology_isIso A B :
    ∀ {n : ℕ}, 2 ≤ n → IsIso (conormalToOmega_lowerShriekHomology A B n))

/- Remark 92.11.5. For `n ≥ 2`, conormal homology identifies with cotangent homology. -/
@[stacks 09D5] #check (Algebra.CotangentComplex.conormalHomology_isIsomorphic_cotangentHomology A B :
    ∀ {n : ℕ}, 2 ≤ n →
      IsIsomorphic (lowerShriekHomology A B (conormalSheaf A B) (-n : ℤ))
        ((cotangentComplex A B).homology (-n : ℤ)))

/- Remark 92.11.5 (7). The degree-minus-two cotangent homology is degree-zero homology
of the first kernel Tor sheaf. -/
@[stacks 09D5] #check
  (Algebra.CotangentComplex.cotangentHomology_negTwo_isIsomorphic_kernelTorHomology_zero A B :
    IsIsomorphic ((cotangentComplex A B).homology (-2))
      (lowerShriekHomology A B (kernelTorSheaf A B 1) 0))
