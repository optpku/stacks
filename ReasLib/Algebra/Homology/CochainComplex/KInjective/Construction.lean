/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction.KInjective
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Grothendieck

/-! # Functorial K-injective replacement

The transfinite attachment foundation and its coded tests assemble the functorial replacement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CochainComplex.KInjectiveResolution.Construction

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The transfinite attachment replacement is K-injective: termwise injectivity and
lifting against bounded acyclic tests give nullhomotopies for acyclic sources. -/
theorem replacement_isKInjective (K : CochainComplex C ℤ) :
    ((replacement C).obj K).IsKInjective :=
  isKInjectiveOfSupply C (SmallAcyclic.subcomplexSupplyOfGenerator C) K

/-- The transfinite replacement functor and its augmentation give a functorial
K-injective resolution. -/
def functorial : CochainComplex.KInjectiveResolution.Functorial C where
  toApproximation :=
    { toFunctor := replacement C
      ι := augmentation C
      mono_app := augmentation_mono C
      quasiIso_app := augmentation_quasiIso C }
  injective := replacement_term_injective C
  isKInjective := replacement_isKInjective C

end CochainComplex.KInjectiveResolution.Construction
