/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineScheme.FinitePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.WeaklyAdic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PresheafColimit
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Formal spectra of adic completions

Canonical evaluation maps compare the quotient-power completion with the formal
spectrum of the inverse-limit completion ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {A : Type u} [CommRing A]

/-- Evaluation at a quotient-power stage defines a weak ideal of definition
of the inverse-limit completion. -/
def evalWeakIdeal (I : Ideal A) (n : ℕ) :
    WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I) :=
  WeakIdealOfDefinition.of (AdicCompletion.WithLimitTopology.evalKernel I n)
    (AdicCompletion.WithLimitTopology.evalKernel_isWeakIdealOfDefinition I n)

/-- The quotient-power spectrum maps to the quotient of the completion by the
kernel of evaluation, via the kernel lift of the canonical evaluation map. -/
def powerStageToLimitStage {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶
      stage (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I)
        (evalWeakIdeal I n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (RingHom.kerLift (AdicCompletion.evalₐ I (n + 1)).toRingHom))) sorry

/-- The evaluation-induced stage maps form a cocone into the presheaf formal
spectrum of the inverse-limit completion. -/
def toSpfLimitCocone {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := PresheafFormalSpectrum.spf (AdicCompletion.WithLimitTopology I)
    (completionStructureHom structureHom I)
  ι :=
    { app n :=
        yoneda.map (powerStageToLimitStage structureHom I n) ≫
          colimit.ι
            (thickenings (AdicCompletion.WithLimitTopology I)
              (completionStructureHom structureHom I) ⋙ yoneda)
            (evalWeakIdeal I n)
      naturality := sorry }

/-- The quotient-power presheaf completion maps canonically to the presheaf
formal spectrum of the inverse-limit completion ring. -/
def toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      PresheafFormalSpectrum.spf (AdicCompletion.WithLimitTopology I)
        (completionStructureHom structureHom I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (toSpfLimitCocone structureHom I)

/-- On each quotient-power stage, the presheaf comparison is induced by the
kernel lift of evaluation followed by the weak-ideal colimit leg. -/
theorem toSpfLimit_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfLimit structureHom I =
      yoneda.map (powerStageToLimitStage structureHom I n) ≫
        colimit.ι
          (thickenings (AdicCompletion.WithLimitTopology I)
            (completionStructureHom structureHom I) ⋙ yoneda)
          (evalWeakIdeal I n) :=
  sorry

/-- The evaluation comparison with the inverse-limit presheaf formal spectrum
is an isomorphism for every ideal. -/
instance isIso_toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) : IsIso (toSpfLimit structureHom I) :=
  sorry

/-- The sheafified quotient-power completion maps canonically to the sheaf
formal spectrum of the inverse-limit completion. -/
def toSpfCompletion {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletionSheaf structureHom I ⟶
      spf (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
    (toSpfLimit structureHom I) ≫
      (spf_iso_sheafify_presheafColimit (AdicCompletion.WithLimitTopology I)
        (completionStructureHom structureHom I)).inv

/-- On each sheafified quotient-power stage, the completion comparison is the
sheafified kernel-lift map followed by the canonical formal-spectrum leg. -/
theorem toSpfCompletion_ι {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfAdicCompletionι structureHom I n) ≫ toSpfCompletion structureHom I =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (powerStageToLimitStage structureHom I n)) ≫
          spfι (AdicCompletion.WithLimitTopology I)
            (completionStructureHom structureHom I) (evalWeakIdeal I n) :=
  sorry

/-- The canonical comparison from the sheafified quotient-power completion to
the sheaf formal spectrum of the inverse-limit completion is an isomorphism. -/
instance instIsIso_toSpfCompletion {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsIso (toSpfCompletion structureHom I) :=
  sorry

/-- The sheafified completion of an affine scheme along any ideal is weakly adic. -/
instance instIsWeaklyAdic_spfAdicCompletionSheaf {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsWeaklyAdic (spfAdicCompletionSheaf structureHom I).obj :=
  sorry

/-- The sheafified completion along a finitely generated ideal is adic*. -/
theorem isAdicStar_of_fg {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    IsAdicStarAffine (spfAdicCompletionSheaf structureHom I).obj :=
  sorry

/-- The sheafified completion of a Noetherian affine scheme along an ideal is
Noetherian. -/
instance instIsNoetherianAffine_spfAdicCompletionSheaf {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [AlgebraicGeometry.IsNoetherian (Spec (.of A))]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsNoetherianAffine (spfAdicCompletionSheaf structureHom I).obj :=
  sorry

/-- Completion along an ideal is weakly adic; for a finitely generated ideal,
the extended ideal defines its adic topology, the canonical formal-spectrum
comparison is an isomorphism, and the completion is adic*. Completion of a
Noetherian affine scheme is Noetherian. -/
theorem completionAlongIdeal_types {S : Scheme.{u}} {A : Type u} [CommRing A]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsWeaklyAdic (spfAdicCompletionSheaf structureHom I).obj ∧
      (I.FG →
        IsAdic (I.map (algebraMap A (AdicCompletion.WithLimitTopology I))) ∧
          IsIso (toSpfCompletion structureHom I) ∧
            IsAdicStarAffine (spfAdicCompletionSheaf structureHom I).obj) ∧
      (AlgebraicGeometry.IsNoetherian (Spec (.of A)) →
        IsNoetherianAffine (spfAdicCompletionSheaf structureHom I).obj) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
