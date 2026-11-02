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
    X.p.obj (objects 0) = Over.mk (adicResidueToS toS) := by
  rw [over_obj 0]
  change AdicPresentation.quotientStage toS (maximalIdeal R ^ 1) = _
  rw [pow_one]
  rfl

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
      adicResidueToS toS := by
  rw [adicResidueToS, ← h_toS, ← Category.assoc, ← Spec.map_comp]
  rfl

include h_toS in
/-- The canonical coefficient-algebra truncation spectrum is the maximal-adic stage over `S`. -/
theorem adicTruncationOver (n : ℕ) :
    specOver openImmersion ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n) =
      AdicPresentation.stage toS (maximalIdeal R) n := by
  unfold specOver AdicPresentation.stage AdicPresentation.quotientStage
  rw [← h_toS, ← Category.assoc, ← Spec.map_comp]
  rfl

variable [LocallyOfFiniteType (adicResidueToS toS)]

include over_obj over_step in
/-- The forward composite from the residue stage lifts the canonical residue spectrum map. -/
theorem adicFromResidue_over (n : ℕ) :
    X.p.IsHomLift
      (specOver_toResidue openImmersion (adicResidueToS toS)
        (adicResidueFactor toS openImmersion h_toS)
        ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncation n))
      (adicFromResidue objects step n) := by
  have hseq : ∀ n, X.p.IsHomLift
      ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.zero_le n)))
      (adicFromResidue objects step n) := by
    intro n
    induction n with
    | zero =>
      change X.p.IsHomLift
        ((AdicPresentation.diagram toS (maximalIdeal R)).map (𝟙 0)) (𝟙 (objects 0))
      rw [CategoryTheory.Functor.map_id]
      exact IsHomLift.id (p := X.p) (over_obj 0)
    | succ n ih =>
      letI := ih
      letI := over_step n
      have hcomp := IsHomLift.comp X.p
        ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.zero_le n)))
        ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.le_succ n)))
        (adicFromResidue objects step n) (step n)
      have htriangle : adicFromResidue objects step (n + 1) =
          adicFromResidue objects step n ≫ step n := by
        change OfSequence.map step 0 (n + 1) _ = OfSequence.map step 0 n _ ≫ step n
        rw [OfSequence.map_comp step 0 n (n + 1) (Nat.zero_le n) (Nat.le_succ n),
          OfSequence.map_le_succ]
      rw [htriangle]
      simpa only [← CategoryTheory.Functor.map_comp, homOfLE_comp] using hcomp
  have hres (r : R) :
      (ArtinianLocalAlgCat.toResidue ((CompleteLocalAlgCat.of (Λ := Λ) R AlgEquiv.refl).truncation n)).hom
        (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) r) = residue R r := by
    rfl
  have hcast {I J K : Ideal R} (e : I = J) (hK : K ≤ I) :
      eqToHom (congrArg (fun L : Ideal R => Spec (CommRingCat.of (R ⧸ L))) e.symm) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hK)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hK.trans (le_of_eq e)))) := by
    cases e
    simp only [eqToHom_refl, Category.id_comp]
  have h0 : Over.mk (adicResidueToS toS) =
      (AdicPresentation.diagram toS (maximalIdeal R)).obj 0 := by
    change Over.mk (adicResidueToS toS) = AdicPresentation.quotientStage toS (maximalIdeal R ^ 1)
    rw [pow_one]
    rfl
  have hmap : specOver_toResidue openImmersion (adicResidueToS toS)
      (adicResidueFactor toS openImmersion h_toS)
      ((CompleteLocalAlgCat.of (Λ := Λ) R AlgEquiv.refl).truncation n) =
      eqToHom h0 ≫
        (AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.zero_le n)) ≫
        eqToHom (adicTruncationOver toS openImmersion h_toS n).symm := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    change Spec.map (CommRingCat.ofHom
      (ArtinianLocalAlgCat.toResidue ((CompleteLocalAlgCat.of (Λ := Λ) R AlgEquiv.refl).truncation n)).hom.toRingHom) =
      eqToHom (congrArg (fun L : Ideal R => Spec (CommRingCat.of (R ⧸ L)))
        (pow_one (maximalIdeal R)).symm) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n))))) ≫ 𝟙 _
    rw [Category.comp_id, hcast (pow_one (maximalIdeal R))]
    apply congrArg (fun f : (R ⧸ maximalIdeal R ^ (n + 1)) →+* ResidueField R =>
      Spec.map (CommRingCat.ofHom f))
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact hres r
  rw [hmap]
  have hcomp := @IsHomLift.lift_comp_eqToHom _ _ _ _ X.p _ _ _ _ _ _ (hseq n) _
    (adicTruncationOver toS openImmersion h_toS n).symm
  exact @IsHomLift.lift_eqToHom_comp _ _ _ _ X.p _ _ _ _ _ _ hcomp _ h0

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
      (step n) := by
  have h : specOverMap openImmersion
      ((CompleteLocalAlgCat.of R AlgEquiv.refl).truncationMap n) =
      eqToHom (adicTruncationOver toS openImmersion h_toS n) ≫
        (AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.le_succ n)) ≫
        eqToHom (adicTruncationOver toS openImmersion h_toS (n + 1)).symm := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left]
    change Spec.map _ = (𝟙 _) ≫ Spec.map _ ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [h]
  letI := over_step n
  have hcomp := IsHomLift.lift_comp_eqToHom X.p
    ((AdicPresentation.diagram toS (maximalIdeal R)).map (homOfLE (Nat.le_succ n)))
    (step n) (adicTruncationOver toS openImmersion h_toS (n + 1)).symm
  exact @IsHomLift.lift_eqToHom_comp _ _ _ _ X.p _ _ _ _ _ _ hcomp _
    (adicTruncationOver toS openImmersion h_toS n)

/-- Forward composites from the residue stage commute with each successor transition. -/
theorem adicStep_triangle (n : ℕ) :
    adicFromResidue objects step (n + 1) = adicFromResidue objects step n ≫ step n := by
  change OfSequence.map step 0 (n + 1) _ = OfSequence.map step 0 n _ ≫ step n
  rw [OfSequence.map_comp step 0 n (n + 1) (Nat.zero_le n) (Nat.le_succ n),
    OfSequence.map_le_succ]

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
      (adicStageMap toS objects step over_obj over_step openImmersion h_toS n) := by
  change (adicProjection toS objects over_obj openImmersion h_toS).IsHomLift
    ((adicProjection toS objects over_obj openImmersion h_toS).map
      (adicStageMap toS objects step over_obj over_step openImmersion h_toS n)) _
  exact IsHomLift.map _ _

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
        (ξ.system.stepMap n) := by
  dsimp only [formalObjectOfAdicSystem, _root_.FormalObject.of, _root_.FormalObject.system,
    SequentialInverseSystem.family, SequentialInverseSystem.stepMap,
    SequentialInverseSystem.transitionMap]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    adicStageMap_over toS objects step over_obj over_step openImmersion h_toS n⟩

end AlgebraicGeometry.GroupoidsOver.Predeformation
