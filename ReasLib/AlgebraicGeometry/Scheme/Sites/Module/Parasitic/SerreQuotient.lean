/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Category
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.Adequate
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# The Serre quotient by parasitic adequate modules

This module records exactness of Zariski restriction, identifies its kernel with
the parasitic object property, and constructs the induced equivalence from the
corresponding Serre quotient to quasicoherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Adeq

namespace ZariskiRestriction

/-- Zariski restriction from adequate modules to quasicoherent modules is exact. -/
theorem exact (S : Scheme.{u}) (τ : StandardTopology) :
    exactFunctor
      (Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (Scheme.QCoh S) (zariskiRestriction S τ) := sorry

/-- Zariski restriction bundled as an exact functor. -/
noncomputable def exactFunctor (S : Scheme.{u}) (τ : StandardTopology) :
    Adeq ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) ⥤ₑ Scheme.QCoh S :=
  ⟨zariskiRestriction S τ, exact S τ⟩

/-- The kernel of Zariski restriction is the property of being parasitic. -/
theorem kernel_eq (S : Scheme.{u}) (τ : StandardTopology) :
    (zariskiRestriction S τ).kernel =
      parasitic ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ) := sorry

end ZariskiRestriction

namespace Parasitic

/-- Parasitic adequate modules form a Serre class. -/
theorem isSerreClass (S : Scheme.{u}) (τ : StandardTopology) :
    @ObjectProperty.IsSerreClass _ _ (instAbelian S τ)
      (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ)) := sorry

/-- The exact functor induced by Zariski restriction on the parasitic Serre quotient. -/
noncomputable def quotientExactFunctor (S : Scheme.{u}) (τ : StandardTopology) :
    (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
        (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))
        (isSerreClass S τ)).Localization ⥤ₑ
      Scheme.QCoh S :=
  @ObjectProperty.SerreClassLocalization.inducedExactFunctor _ _
    (instAbelian S τ)
    (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
      (@affineEvaluationUnderlying S τ))
    (isSerreClass S τ) _ _ _
    (ZariskiRestriction.exactFunctor S τ) (ZariskiRestriction.kernel_eq S τ).ge

/-- The functor underlying Zariski restriction on the parasitic Serre quotient. -/
noncomputable abbrev quotientFunctor (S : Scheme.{u}) (τ : StandardTopology) :
    (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
        (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))
        (isSerreClass S τ)).Localization ⥤
      Scheme.QCoh S :=
  (quotientExactFunctor S τ).obj

/-- The quotient functor followed by induced Zariski restriction recovers Zariski
restriction itself. -/
noncomputable def quotientCompIso (S : Scheme.{u}) (τ : StandardTopology) :
    (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
          (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
            (@affineEvaluationUnderlying S τ))
          (isSerreClass S τ)).Q ⋙
        quotientFunctor S τ ≅
      zariskiRestriction S τ :=
  Localization.fac (ZariskiRestriction.exactFunctor S τ).obj
    (((@ObjectProperty.isoModSerre_isInvertedBy_iff _ _ (instAbelian S τ) _ _ _
        (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))
        (isSerreClass S τ)
        (ZariskiRestriction.exactFunctor S τ).obj).2
      (ZariskiRestriction.kernel_eq S τ).ge))
    (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
      (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (isSerreClass S τ)).Q

/-- Association followed by the canonical quotient is the concrete quasi-inverse to
induced Zariski restriction. -/
noncomputable def quasiInverse (S : Scheme.{u}) (τ : StandardTopology) :
    Scheme.QCoh S ⥤
      (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
        (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
          (@affineEvaluationUnderlying S τ))
        (isSerreClass S τ)).Localization :=
  associated S τ ⋙
    (@ObjectProperty.isoModSerre _ _ (instAbelian S τ)
      (parasitic ModuleValuedFunctor.tensorExtensionUnderlying
        (@affineEvaluationUnderlying S τ))
      (isSerreClass S τ)).Q

/-- Induced Zariski restriction and association followed by the quotient are
quasi-inverse. -/
theorem isQuasiInverse (S : Scheme.{u}) (τ : StandardTopology) :
    (quotientFunctor S τ).IsQuasiInverse (quasiInverse S τ) := sorry

/-- Induced Zariski restriction is an equivalence from the parasitic Serre quotient. -/
theorem isEquivalence (S : Scheme.{u}) (τ : StandardTopology) :
    (quotientFunctor S τ).IsEquivalence := sorry

end Parasitic

end SheafOfModules.Adeq
