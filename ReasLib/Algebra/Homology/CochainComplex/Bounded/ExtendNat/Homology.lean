/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the nonnegative extension

Extension by zero from nonnegative cochain complexes does not change homology in a nonnegative
degree.  This file records the canonical comparison after bounded-below derived localization.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v u

namespace CochainComplex.Plus

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical objectwise comparison between derived homology after extension by zero and
ordinary homology of a nonnegative cochain complex. -/
noncomputable def extendNatDerivedHomologyIsoApp (K : CochainComplex C ℕ) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C (p : ℤ)).obj
          (DerivedCategory.Plus.Q.obj ((extendNat C).obj K)) ≅
        (HomologicalComplex.homologyFunctor C (up ℕ) p).obj K :=
  (DerivedCategory.homologyFunctor C (p : ℤ)).mapIso
      ((DerivedCategory.Plus.Qh.compInclusionIso C).app ((extendNat C).obj K)) ≪≫
    (DerivedCategory.homologyFunctorFactors C (p : ℤ)).app
      ((extendNat C).obj K).obj ≪≫
    K.extendHomologyIso embeddingUpNat rfl

/-- The objectwise extension-homology comparisons are natural in the nonnegative complex. -/
theorem extendNatDerivedHomologyIsoApp_naturality
    {K L : CochainComplex C ℕ} (f : K ⟶ L) (p : ℕ) :
    (extendNat C ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor C (p : ℤ)).map f ≫
        (extendNatDerivedHomologyIsoApp C L p).hom =
      (extendNatDerivedHomologyIsoApp C K p).hom ≫
        (HomologicalComplex.homologyFunctor C (up ℕ) p).map f := sorry

/-- Extending a nonnegative cochain complex by zero, localizing in `D⁺(C)`, and taking
degree-`p` homology canonically recovers its ordinary degree-`p` homology. -/
@[stacks 01EQ "homology of the nonnegative derived extension"]
noncomputable def extendNatDerivedHomologyIso (p : ℕ) :
    extendNat C ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor C (p : ℤ) ≅
      HomologicalComplex.homologyFunctor C (up ℕ) p :=
  NatIso.ofComponents
    (fun K ↦ extendNatDerivedHomologyIsoApp C K p)
    (fun f ↦ extendNatDerivedHomologyIsoApp_naturality C f p)

end CochainComplex.Plus


