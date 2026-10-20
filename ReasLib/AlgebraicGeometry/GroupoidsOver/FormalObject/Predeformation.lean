/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Adic systems as formal objects of a residue-point predeformation category

A forward system over the maximal-adic quotient spectra gives an inverse system
of residue lifts over the canonical Artinian truncations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S}
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
variable (toS : Spec (CommRingCat.of R) ⟶ S)

/-- The residue-field point induced by a structure morphism from a local ring spectrum. -/
def adicResidueToS : Spec (CommRingCat.of (ResidueField R)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (residue R)) ≫ toS

variable (objects : ℕ → X.total) (step : ∀ n, objects n ⟶ objects (n + 1))
variable (over_obj : ∀ n, X.p.obj (objects n) =
  AdicPresentation.stage toS (maximalIdeal R) n)
variable (over_step : ∀ n, X.p.IsHomLift
  ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.le_succ n))) (step n))

include over_obj in
/-- The zeroth maximal-adic stage lies over the residue-field point. -/
theorem adicResidueFiber_over :
    X.p.obj (objects 0) = Over.mk (adicResidueToS toS) := sorry

/-- The actual zeroth stage, viewed in the fibre over the residue-field spectrum. -/
def adicResidueFiber : X.p.Fiber (Over.mk (adicResidueToS toS)) :=
  Fiber.mk (adicResidueFiber_over toS objects over_obj)

/-- The composite of the supplied forward transitions from stage zero to stage `n`. -/
def adicFromResidue (n : ℕ) : objects 0 ⟶ objects n :=
  (Functor.ofSequence step).map (homOfLE (Nat.zero_le n))

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [Algebra Λ R] [Module.Finite Λ (ResidueField R)]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (h_toS : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ openImmersion = toS)

include h_toS in
/-- The residue-field structure morphism factors through the chosen affine open. -/
theorem adicResidueFactor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField R))) ≫ openImmersion =
      adicResidueToS toS := sorry

include h_toS in
/-- The canonical coefficient-algebra truncation spectrum is the maximal-adic stage over `S`. -/
theorem adicTruncationOver (n : ℕ) :
    specOver openImmersion ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n) =
      AdicPresentation.stage toS (maximalIdeal R) n := sorry

variable [LocallyOfFiniteType (adicResidueToS toS)]

include over_obj over_step in
/-- The forward composite from the residue stage lifts the canonical residue spectrum map. -/
theorem adicFromResidue_over (n : ℕ) :
    X.p.IsHomLift
      (specOver_toResidue openImmersion (adicResidueToS toS)
        (adicResidueFactor toS openImmersion h_toS)
        ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n))
      (adicFromResidue objects step n) := sorry

/-- The original stage with its composite from the residue object over the canonical truncation. -/
def adicObject (n : ℕ) :
    Obj openImmersion (adicResidueToS toS) (adicResidueFactor toS openImmersion h_toS)
      X (adicResidueFiber toS objects over_obj) where
  base := (CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n
  target := Fiber.mk ((over_obj n).trans (adicTruncationOver toS openImmersion h_toS n).symm)
  fromResidue := adicFromResidue objects step n
  over_fromResidue := adicFromResidue_over toS objects step over_obj over_step openImmersion h_toS n

include over_obj over_step h_toS in
/-- A supplied forward transition lifts the spectrum map of the canonical truncation projection. -/
theorem adicStep_over (n : ℕ) :
    X.p.IsHomLift
      (specOverMap openImmersion ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncationMap n))
      (step n) := sorry

/-- Forward composites from the residue stage commute with each successor transition. -/
theorem adicStep_triangle (n : ℕ) :
    adicFromResidue objects step (n + 1) = adicFromResidue objects step n ≫ step n := sorry

/-- The original forward arrow as a reversed predeformation arrow over a truncation projection. -/
def adicStep (n : ℕ) :
    Hom (adicObject toS objects step over_obj over_step openImmersion h_toS (n + 1))
      (adicObject toS objects step over_obj over_step openImmersion h_toS n) where
  baseHom := (CompleteLocalAlgCat.of R AlgEquiv.refl).truncationMap n
  hom := step n
  over_hom := adicStep_over toS objects step over_obj over_step openImmersion h_toS n
  triangle := adicStep_triangle objects step n

/-- The predeformation stage with its morphism universe lifted. -/
def adicStage (n : ℕ) :
    ULiftHom.{u + 1}
      (Obj openImmersion (adicResidueToS toS) (adicResidueFactor toS openImmersion h_toS)
        X (adicResidueFiber toS objects over_obj)) :=
  ULiftHom.objUp (adicObject toS objects step over_obj over_step openImmersion h_toS n)

/-- The lifted successor transition induced by the supplied forward arrow. -/
def adicStageMap (n : ℕ) :
    adicStage toS objects step over_obj over_step openImmersion h_toS (n + 1) ⟶
      adicStage toS objects step over_obj over_step openImmersion h_toS n :=
  (ULiftHom.up :
      Obj openImmersion (adicResidueToS toS) (adicResidueFactor toS openImmersion h_toS)
        X (adicResidueFiber toS objects over_obj) ⥤ ULiftHom.{u + 1} _).map
    (adicStep toS objects step over_obj over_step openImmersion h_toS n)

/-- The residue-lift projection after forgetting the morphism-universe lift. -/
def adicProjection :
    ULiftHom.{u + 1}
      (Obj openImmersion (adicResidueToS toS) (adicResidueFactor toS openImmersion h_toS)
        X (adicResidueFiber toS objects over_obj)) ⥤ ArtinianLocalAlgCat Λ (ResidueField R) :=
  ULiftHom.down ⋙ predeformationFunctor X openImmersion (adicResidueToS toS)
    (adicResidueFactor toS openImmersion h_toS) (adicResidueFiber toS objects over_obj)

/-- The lifted successor transition lies over the canonical truncation projection. -/
theorem adicStageMap_over (n : ℕ) :
    (adicProjection toS objects over_obj openImmersion h_toS).IsHomLift
      ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncationMap n)
      (adicStageMap toS objects step over_obj over_step openImmersion h_toS n) := sorry

/-- A maximal-adic forward system defines a formal object of its residue-point predeformation category. -/
def formalObjectOfAdicSystem :
    _root_.FormalObject (adicProjection toS objects over_obj openImmersion h_toS) :=
  _root_.FormalObject.of
    (CompleteLocalAlgCat.of R AlgEquiv.refl)
    (adicStage toS objects step over_obj over_step openImmersion h_toS)
    (adicStageMap toS objects step over_obj over_step openImmersion h_toS)
    (fun _ => rfl)
    (adicStageMap_over toS objects step over_obj over_step openImmersion h_toS)

/-- The formal object constructed from an adic system has the supplied complete local base. -/
theorem formalObjectOfAdicSystem_base :
    (formalObjectOfAdicSystem toS objects step over_obj over_step openImmersion h_toS).base =
      CompleteLocalAlgCat.of R AlgEquiv.refl := rfl

/-- The constructed formal object retains the original stages and transitions and their truncation projections. -/
theorem formalObjectOfAdicSystem_spec (n : ℕ) :
    let ξ := formalObjectOfAdicSystem toS objects step over_obj over_step openImmersion h_toS
    let p := adicProjection toS objects over_obj openImmersion h_toS
    ξ.system.family n = adicStage toS objects step over_obj over_step openImmersion h_toS n ∧
      ULiftHom.down.map (ξ.system.stepMap n) =
        adicStep toS objects step over_obj over_step openImmersion h_toS n ∧
      Fiber.fiberInclusion.obj
        (adicObject toS objects step over_obj over_step openImmersion h_toS n).target = objects n ∧
      (adicStep toS objects step over_obj over_step openImmersion h_toS n).hom = step n ∧
      p.obj (ξ.system.family n) = (CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n ∧
      p.IsHomLift ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncationMap n)
        (ξ.system.stepMap n) := sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
