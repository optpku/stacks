/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Adequate
public import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient.Equivalence
public import stacks_project.Chap46.Lemma_46_6_2_Quotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite
open AlgebraicGeometry
open SerreClassLocalization.Derived ExactFunctor.Derived
open Equivalence.MapDerivedCategory

noncomputable section

universe u

variable (S : Scheme.{u}) (τ : StandardTopology)
variable [HasDerivedCategory.{u}
  (SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
    (@SheafOfModules.affineEvaluationUnderlying S τ))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
    (@SheafOfModules.affineEvaluationUnderlying S τ)).isoModSerre.Localization]
variable [HasDerivedCategory.{u} (Scheme.QCoh S)]

/- Lemma 46.7.1 (1): the unbounded derived category of adequate modules, localized at
complexes with parasitic cohomology, is the derived category of quasicoherent modules. -/
@[stacks 06ZQ] #check
  (CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Quotient.isLocalization_comp_equivalence_of_adjunction
    (P := SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ))
    (e := (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)
    (u := SheafOfModules.Adeq.associated S τ)
    (adj := (SheafOfModules.Adeq.adjunction S τ).ofNatIsoRight
      (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm)
    (h_unit := inferInstanceAs (IsIso
      ((SheafOfModules.Adeq.adjunction S τ).unit ≫
        Functor.whiskerLeft (SheafOfModules.Adeq.associated S τ)
          (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm.hom))) :
      (((SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@SheafOfModules.affineEvaluationUnderlying S τ)).isoModSerre.Q.mapDerivedCategory) ⋙
          Equivalence.MapDerivedCategory.functor
            (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence).IsLocalization
        (DerivedCategory.cohomologyIn
          (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@SheafOfModules.affineEvaluationUnderlying S τ))).trW)

/- Lemma 46.7.1 (2): the bounded-below derived category of adequate modules, localized at
complexes with parasitic cohomology, is the bounded-below derived category of quasicoherent
modules. -/
@[stacks 06ZQ] #check
  (CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.isLocalization_comp_equivalence_of_adjunction
    (P := SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ))
    (e := (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)
    (u := SheafOfModules.Adeq.associated S τ)
    (adj := (SheafOfModules.Adeq.adjunction S τ).ofNatIsoRight
      (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm)
    (h_unit := inferInstanceAs (IsIso
      ((SheafOfModules.Adeq.adjunction S τ).unit ≫
        Functor.whiskerLeft (SheafOfModules.Adeq.associated S τ)
          (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm.hom))) :
      ((Plus.Quotient.functor
            (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
              (@SheafOfModules.affineEvaluationUnderlying S τ))) ⋙
          Plus.functor (forwardExact
            (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)).IsLocalization
        (DerivedCategory.Plus.cohomologyIn
          (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@SheafOfModules.affineEvaluationUnderlying S τ))).trW)

/- Lemma 46.7.1 (3): the bounded-above derived category of adequate modules, localized at
complexes with parasitic cohomology, is the bounded-above derived category of quasicoherent
modules. -/
@[stacks 06ZQ] #check
  (CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.isLocalization_comp_equivalence_of_adjunction
    (P := SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ))
    (e := (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)
    (u := SheafOfModules.Adeq.associated S τ)
    (adj := (SheafOfModules.Adeq.adjunction S τ).ofNatIsoRight
      (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm)
    (h_unit := inferInstanceAs (IsIso
      ((SheafOfModules.Adeq.adjunction S τ).unit ≫
        Functor.whiskerLeft (SheafOfModules.Adeq.associated S τ)
          (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm.hom))) :
      ((Minus.Quotient.functor
            (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
              (@SheafOfModules.affineEvaluationUnderlying S τ))) ⋙
          Minus.functor (forwardExact
            (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)).IsLocalization
        (DerivedCategory.Minus.cohomologyIn
          (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@SheafOfModules.affineEvaluationUnderlying S τ))).trW)

/- Lemma 46.7.1 (4): the bounded derived category of adequate modules, localized at
complexes with parasitic cohomology, is the bounded derived category of quasicoherent modules. -/
@[stacks 06ZQ] #check
  (CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.isLocalization_comp_equivalence_of_adjunction
    (P := SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ))
    (e := (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)
    (u := SheafOfModules.Adeq.associated S τ)
    (adj := (SheafOfModules.Adeq.adjunction S τ).ofNatIsoRight
      (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm)
    (h_unit := inferInstanceAs (IsIso
      ((SheafOfModules.Adeq.adjunction S τ).unit ≫
        Functor.whiskerLeft (SheafOfModules.Adeq.associated S τ)
          (SheafOfModules.Adeq.Parasitic.quotientCompIso S τ).symm.hom))) :
      ((Bounded.Quotient.functor
            (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
              (@SheafOfModules.affineEvaluationUnderlying S τ))) ⋙
          Bounded.functor (forwardExact
            (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).asEquivalence)).IsLocalization
        (DerivedCategory.Bounded.cohomologyIn
          (SheafOfModules.Adeq.parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@SheafOfModules.affineEvaluationUnderlying S τ))).trW)
