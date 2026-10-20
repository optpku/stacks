/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Cohomology.FiniteFreeLocus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived.FiniteFree
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTriple

variable {X : Scheme.{u}}

/-- A good effective-Cartier-divisor and perfect-derived-module triple admits a finitely
presented closed subscheme containing the maximal finite-free locus on the divisor. On this
subscheme, the pulled-back derived η-complex has finite locally free cohomology, and its stalk
ranks agree with those of the original complex over that locus. -/
@[stacks 0GTZ]
theorem existsEtaFlattening (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M)
    (h_good : AlgebraicGeometry.Scheme.IsGoodTriple D M) :
    ∃ J : D.subscheme.IdealSheafData, let T := J.subscheme;
        Scheme.Hom.FinitePresentation J.subschemeι ∧
        J ≤ ((D.subschemeι ⁻¹ᵁ
          finiteFreeOpen hM (fun x ↦ inferInstance)).ι).ker ∧
        finiteLocallyFreeOn
          ((RingedSpace.modulePullbackDerived
            (J.subschemeι ≫ D.subschemeι).toShHom).obj
              ((functor D.toSubobject).obj M)) ⊤ ∧
        ∀ (n : ℤ) (t : T),
          (J.subschemeι ≫ D.subschemeι) t ∈
              finiteFreeOpen hM (fun x ↦ inferInstance) →
            Module.rank (X.presheaf.stalk ((J.subschemeι ≫ D.subschemeι) t))
                (M.cohomologyStalk n ((J.subschemeι ≫ D.subschemeι) t)) =
              Module.rank (T.presheaf.stalk t)
                (cohomologyStalk ((RingedSpace.modulePullbackDerived
                  (J.subschemeι ≫ D.subschemeι).toShHom).obj
                    ((functor D.toSubobject).obj M)) n t) := sorry

end AlgebraicGeometry.Scheme.IsGoodTriple
