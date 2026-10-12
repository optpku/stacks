/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_StagePDConnection
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_ReindexedSemilinearLimit

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CrystallineModuleSheaf CechCrisCover CrystallineStagePDConnection
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace CrystallineCrossStage

variable {p : ℕ} [Fact p.Prime]
variable {A C C' : Type u} [CommRing A] [CommRing C] [CommRing C']
variable [Algebra A C] [Algebra A C']
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (hIC : Ideal.map (algebraMap A C) IA = ⊥) (hpnil : IsNilpotent (p : C))
variable (hIC' : Ideal.map (algebraMap A C') IA = ⊥) (hpnil' : IsNilpotent (p : C'))
variable {X : Scheme.{u}} (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable (eX : Spec (.of C) ⟶ X) (eX' : Spec (.of C') ⟶ X)
variable (heX : eX ≫ x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (heX' : eX' ≫ x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C')))
variable (hI : I = DividedPowers.affineIdeal (I := IA))
variable (hγ : DividedPowers.IsDPMorphism γA
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (ho : IsOpenImmersion eX) (ho' : IsOpenImmersion eX')
variable (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil)
variable (W : CompletedCrisObject p A IA γA C' (algebraMap A C') hIC' hpnil')
variable (φ : DividedPowers.DPMorphism Z.B.dividedPowers W.B.dividedPowers)
variable (g : C →+* C')
variable (hbase : φ.toRingHom.comp Z.base.toRingHom = W.base.toRingHom)
variable (hquot : W.toC.comp φ.toRingHom = g.comp Z.toC)
variable (hchart : Spec.map (CommRingCat.ofHom g) ≫ eX = eX')
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [hcoherent : CrystallineCoefficients.SectionsCoherent I γS hc x₀ F]

/-- The actual cross-chart coefficient map at a sufficiently deep source
stage. It uses F's comparison along the geometric PD map, not an arbitrary
identification of coefficient carriers. -/
noncomputable def stageMap (e : ℕ) :
    envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F
        (crossStageIndex γA hIC' hpnil' W e) ⟶
      (ModuleCat.restrictScalars φ.toRingHom).obj
        (envelopeModule γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F e) := by
  -- Local instance justification (defeq pin): target sections carry the
  -- source envelope action restricted along this particular cross-chart map.
  -- Local instance justification (defeq pin): target sections restrict scalars along this particular cross-chart map.
  letI : Module Z.B (envelopeModule γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F e) :=
    ((ModuleCat.restrictScalars φ.toRingHom).obj
      (envelopeModule γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F e)).isModule
  exact ModuleCat.ofHom
    { toFun := abelianGlobalSections_map
        (crossSmallStageMap γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
          hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart e).hom.thickening
        (F.comparison (crossSmallStageMap γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
          hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart e))
      map_add' := map_add _
      map_smul' := sorry }

include hcoherent in
/-- Coherence of F and the geometric cross-stage squares ensure naturality
of the actual coefficient restrictions, including both stage offsets. -/
theorem stageMap_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (((crossStageIndex γA hIC' hpnil' W).monotone.functor.op) ⋙
      envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).map f ≫
        stageMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
          φ g hbase hquot hchart F j.unop =
      stageMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
          φ g hbase hquot hchart F i.unop ≫
        (envelopeSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F ⋙
          ModuleCat.restrictScalars φ.toRingHom).map f := sorry

/-- The cross-chart natural transformation retains the explicit geometric
stage maps and the source reindexing required by different offsets. -/
noncomputable def stageTransformation :
    ((crossStageIndex γA hIC' hpnil' W).monotone.functor.op) ⋙
        envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F ⟶
      envelopeSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F ⋙
        ModuleCat.restrictScalars φ.toRingHom where
  app e := stageMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
    φ g hbase hquot hchart F e.unop
  naturality := fun _ _ f ↦ stageMap_naturality γA hIC hpnil hIC' hpnil' I γS hc x₀
    eX eX' heX heX' hI hγ ho ho' Z W φ g hbase hquot hchart F f

/-- The actual semilinear comparison of completed crystal coefficients,
formed from their compatible reindexed geometric stage restrictions. -/
noncomputable def coefficientMap :
    completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F →ₛₗ[φ.toRingHom]
      completedModule γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F :=
  CrystallineReindexedLimit.map φ.toRingHom
    (envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)
    (envelopeSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F)
    ((crossStageIndex γA hIC' hpnil' W).monotone.functor.op)
    (stageTransformation γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
      φ g hbase hquot hchart F)

/-- Each projection of the completed coefficient comparison is the actual
geometric restriction from the correctly shifted source stage. -/
theorem coefficientMap_projection (e : ℕ)
    (x : completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F) :
    coefficientProjection γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F e
      (coefficientMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
        φ g hbase hquot hchart F x) =
      stageMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
        φ g hbase hquot hchart F e
        (coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F
          (crossStageIndex γA hIC' hpnil' W e) x) :=
  CrystallineReindexedLimit.map_projection φ.toRingHom
    (envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)
    (envelopeSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F)
    ((crossStageIndex γA hIC' hpnil' W).monotone.functor.op)
    (stageTransformation γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
      φ g hbase hquot hchart F) (op e) x

/-- The target envelope is an algebra over the source through its actual
PD morphism. -/
noncomputable abbrev envelopeMapAlgebra : Algebra Z.B W.B := φ.toRingHom.toAlgebra

include hbase in
/-- The cross-envelope algebra respects the original base-ring action. -/
theorem envelopeMapTower :
  -- Local instance justification (noncanonical choice): the supplied PD morphism fixes this cross-envelope action.
  letI : Algebra Z.B W.B := envelopeMapAlgebra γA hIC hpnil hIC' hpnil' Z W φ
  IsScalarTower A Z.B W.B := sorry

/-- The actual semilinear map of algebraic PD one-forms. -/
noncomputable def algebraicOneFormsMap :
    CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers →ₛₗ[φ.toRingHom]
      CrystallinePDDeRham.oneForms A W.B W.B.dividedPowers := by
  -- Local instance justification (noncanonical choice): this algebra is
  -- determined by the supplied cross-chart PD morphism, not by the rings alone.
  -- Local instance justification (noncanonical choice): the supplied PD morphism fixes this cross-envelope action.
  letI : Algebra Z.B W.B := envelopeMapAlgebra γA hIC hpnil hIC' hpnil' Z W φ
  -- Local instance justification (noncanonical choice): hbase supplies the tower for this specific PD morphism.
  letI : IsScalarTower A Z.B W.B := envelopeMapTower γA hIC hpnil hIC' hpnil' Z W φ hbase
  exact CrystallinePDDeRham.mapOneForms A Z.B W.B Z.B.dividedPowers W.B.dividedPowers
    φ.isDPMorphism

/-- Complete the true PD form map by its additive p-power-preserving
action on every quotient; the scalar law is separate proof debt. -/
noncomputable def oneFormsMap :
    completedOneForms γA hIC hpnil Z →ₛₗ[φ.toRingHom]
      completedOneForms γA hIC' hpnil' W where
  toFun := FilteredAdditiveCompletion.pAdicMap
    (algebraicOneFormsMap γA hIC hpnil hIC' hpnil' Z W φ hbase).toAddMonoidHom p
  map_add' := map_add _
  map_smul' := sorry

/-- Cross-chart comparison maps both the completed coefficient and the
completed PD forms before taking the outer tensor completion. -/
noncomputable def tensorMap (m : ℕ) :
    completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m →+
      completedTensorTerm γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F m := by
  -- Local instance justification (noncanonical choice): exterior scalar
  -- transport is along this explicit PD morphism.
  -- Local instance justification (noncanonical choice): the supplied PD morphism fixes this cross-envelope action.
  letI : Algebra Z.B W.B := envelopeMapAlgebra γA hIC hpnil hIC' hpnil' Z W φ
  exact FilteredAdditiveCompletion.pAdicMap
    (TensorProduct.map
      (coefficientMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
        φ g hbase hquot hchart F)
      (CrystallineSemilinearForms.map (R := Z.B) (S := W.B)
        (oneFormsMap γA hIC hpnil hIC' hpnil' Z W φ hbase) m)).toAddMonoidHom p

variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]

/-- Naturality of the crystal PD connection and exterior differential,
checked after every shifted stage projection, makes the actual tensor map
commute with the completed differentials. -/
theorem tensorMap_differential (m : ℕ)
    (x : completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    tensorMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
        φ g hbase hquot hchart F (m + 1)
        (completedDifferential γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) =
      completedDifferential γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F m
        (tensorMap γA hIC hpnil hIC' hpnil' I γS hc x₀ eX eX' heX heX' hI hγ ho ho' Z W
          φ g hbase hquot hchart F m x) := sorry

end CrystallineCrossStage
