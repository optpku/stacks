/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.LowerShriek.ProjectionFormula
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Complex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded modules on a localized ringed site

This file specializes the reusable DG lower-shriek and projection-formula API to restriction from
a commutative ringed site to the slice over an object.  All monoidal and adjunction data are
inferred from the global localization instances; callers only provide the site, the object, and
the coefficient DGA.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).LaxMonoidal]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]

#synth (SheafOfModules.RingedSite.Localization.restrictionComplex O U).LaxMonoidal

/-- Restriction of a DGA to the localized ringed site, obtained by applying termwise monoidal
restriction to its underlying complex and operations. -/
@[stacks 0FRV "localized differential graded algebra"]
noncomputable def restrictedAlgebra (A : DGA(O)) : DGA(O.over U) :=
  LowerShriek.restrictedAlgebra
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (R := SheafOfModules.RingedSite.Localization.restrictionComplex O U) A

/-- Restriction of right DG modules to the localized ringed site. -/
@[stacks 0FRW "localized restriction of right DG modules"]
noncomputable def restriction (A : DGA(O)) :
    Mod(A, d) ⥤ Mod((restrictedAlgebra O U A), d) :=
  LowerShriek.restriction
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (R := SheafOfModules.RingedSite.Localization.restrictionComplex O U) A

/-- Restriction of left DG modules to the localized ringed site. -/
@[stacks 0FRX "localized restriction of left DG modules"]
noncomputable def restrictionLeft (A : DGA(O)) :
    LMod(A, d) ⥤ LMod((restrictedAlgebra O U A), d) :=
  LowerShriek.restrictionLeft
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (R := SheafOfModules.RingedSite.Localization.restrictionComplex O U) A

/-- Extension by zero of right DG modules from the localized ringed site. -/
@[stacks 0FRW "localized lower shriek of right DG modules"]
noncomputable def lowerShriek (A : DGA(O)) :
    Mod((restrictedAlgebra O U A), d) ⥤ Mod(A, d) :=
  LowerShriek.functor
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A

/-- Lemma 24.19.1 (0FRW), adjunction form: DG extension by zero is left adjoint to DG
restriction. -/
@[stacks 0FRW "localized DG lower-shriek restriction adjunction"]
noncomputable def adjunction (A : DGA(O)) :
    lowerShriek O U A ⊣ restriction O U A :=
  LowerShriek.adjunction
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A

/-- Lemma 24.19.1 (0FRW): the canonical Hom equivalence for DG extension by zero and
restriction. -/
@[stacks 0FRW "localized DG lower-shriek restriction Hom equivalence"]
noncomputable def homEquiv (A : DGA(O))
    (M : Mod((restrictedAlgebra O U A), d)) (N : Mod(A, d)) :
    ((lowerShriek O U A).obj M ⟶ N) ≃
      (M ⟶ (restriction O U A).obj N) :=
  LowerShriek.homEquiv
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A M N

namespace ProjectionFormula

/-- The left side of the localized DG projection formula as a curried bifunctor. -/
@[stacks 0FRX "localized DG projection formula source"]
noncomputable def sourceFunctor (A : DGA(O)) :
    Mod((restrictedAlgebra O U A), d) ⥤ LMod(A, d) ⥤
      CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ :=
  LowerShriek.ProjectionFormula.sourceFunctor
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A

/-- The right side of the localized DG projection formula as a curried bifunctor. -/
@[stacks 0FRX "localized DG projection formula target"]
noncomputable def targetFunctor (A : DGA(O)) :
    Mod((restrictedAlgebra O U A), d) ⥤ LMod(A, d) ⥤
      CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ :=
  LowerShriek.ProjectionFormula.targetFunctor
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (L := SheafOfModules.RingedSite.Localization.lowerShriekComplex O U)
    (R := SheafOfModules.RingedSite.Localization.restrictionComplex O U) A

/-- Lemma 24.19.2 (0FRX), objectwise form: extension by zero commutes with relative tensor
against an ambient left DG module. -/
@[stacks 0FRX "localized DG projection formula"]
noncomputable def iso (A : DGA(O))
    (M : Mod((restrictedAlgebra O U A), d)) (N : LMod(A, d)) :
    tensor ((lowerShriek O U A).obj M) N ≅
      (SheafOfModules.RingedSite.Localization.lowerShriekComplex O U).obj
        (tensor M ((restrictionLeft O U A).obj N)) :=
  LowerShriek.ProjectionFormula.iso
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A M N

/-- Lemma 24.19.2 (0FRX), functorial form: the localized DG projection formula is natural in
both module variables. -/
@[stacks 0FRX "localized DG projection formula natural in both variables"]
noncomputable def natIso (A : DGA(O)) :
    sourceFunctor O U A ≅ targetFunctor O U A :=
  LowerShriek.ProjectionFormula.natIso
    (JC := J.over U) (JD := J) (OC := O.over U) (OD := O)
    (SheafOfModules.RingedSite.Localization.complexAdjunction O U) A

/-- The bifunctorial localized projection formula has the objectwise comparison `iso`. -/
@[simp]
theorem natIso_app_app (A : DGA(O))
    (M : Mod((restrictedAlgebra O U A), d)) (N : LMod(A, d)) :
    ((natIso O U A).app M).app N = iso O U A M N := sorry

end ProjectionFormula

end SheafOfModules.RingedSite.DifferentialGradedModule.Localization

end
