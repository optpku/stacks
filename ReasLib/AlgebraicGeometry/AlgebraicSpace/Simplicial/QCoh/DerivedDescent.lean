/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Deformation
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Unbounded quasi-coherent descent along fppf hypercoverings -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Functor
open scoped Simplicial

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived

section DualWitness

universe c₁ c₂ c₃ v₁ v₂ v₃

/-- Opposite universal extension maps give the dual universal maps with their original components. -/
private def dualWitness {C : Type c₁} {D : Type c₂} {H : Type c₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
    (L : C ⥤ D) (F : C ⥤ H) (T : D ⥤ H) (c : (L ⋙ T).op ⟶ F.op)
    (w : (Functor.RightExtension.mk (L := L.op) (F := F.op) T.op c).IsUniversal) :
    (Functor.LeftExtension.mk T c.removeOp).IsUniversal := by
  let lift (E : Functor.LeftExtension L F) : T ⟶ E.right :=
    (w.lift (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom))).removeOp
  have fac (E : Functor.LeftExtension L F) :
      c.removeOp ≫ Functor.whiskerLeft L (lift E) = E.hom := by
    ext A
    exact congrArg (fun t ↦ (t.app (Opposite.op A)).unop)
      (w.fac (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom)))
  refine IsInitial.ofUniqueHom (fun E ↦ StructuredArrow.homMk (lift E) (fac E)) ?_
  intro E m
  apply StructuredArrow.hom_ext
  have hm : Functor.whiskerLeft L.op (NatTrans.op m.right) ≫ c = (NatTrans.op E.hom) := by
    ext A
    exact congrArg (fun t ↦ (t.app A.unop).op) (StructuredArrow.w m)
  have h := w.hom_ext (hm.trans (w.fac
    (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom))).symm)
  ext A
  exact congrArg (fun t ↦ (t.app (Opposite.op A)).unop) h

end DualWitness

section RightModel

universe w uC vC uD vD wC wD h vH

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]

/-- The K-injective deformation supplies actual initial extension maps after postcomposition. -/
private theorem rightModel_postcompose {H : Type h} [Category.{vH} H]
    (G : DerivedCategory D ⥤ H) :
    (Functor.KInjectiveModel.derived F ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (Functor.KInjectiveModel.Homotopy.unit F) G ≫
        (Functor.associator DerivedCategory.Qh (Functor.KInjectiveModel.derived F) G).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh (C := C)
  let U := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  let T := Functor.KInjectiveModel.derived F
  let FH := Functor.Homotopy.toDerived F
  let α := Functor.whiskerRight (Functor.KInjectiveModel.Homotopy.unit F) G ≫
    (Functor.associator L T G).hom
  let e₀ : (q ⋙ L) ⋙ T ≅ R ⋙ (q ⋙ FH) :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) T ≪≫
      Functor.KInjectiveModel.fac F ≪≫
      Functor.isoWhiskerLeft R (Functor.Homotopy.cochainIso F).symm
  let e : (q ⋙ L) ⋙ (T ⋙ G) ≅ R ⋙ ((q ⋙ FH) ⋙ G) :=
    (Functor.associator (q ⋙ L) T G).symm ≪≫
      Functor.isoWhiskerRight e₀ G ≪≫ Functor.associator R (q ⋙ FH) G
  -- Local instance justification (defeq pin): opposite deformation uses precisely the original standard composite localization on cochain complexes.
  letI : (q ⋙ L).IsLocalization U :=
    Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso C).symm
  have hη (A : (CochainComplex C ℤ)ᵒᵖ) : U.op ((NatTrans.op η).app A) :=
    CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C A.unop
  have hAug (A : (CochainComplex C ℤ)ᵒᵖ) :
      IsIso ((((q ⋙ FH) ⋙ G).op).map ((NatTrans.op η).app (R.op.obj A))) := by
    -- Local instance justification (proof-local temporary data): both endpoints of this augmentation are the specified K-injective replacements.
    letI : (R.obj A.unop).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C A.unop
    -- Local instance justification (proof-local temporary data): the second endpoint is the replacement of the first specified K-injective model.
    letI : (R.obj (R.obj A.unop)).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C
        (R.obj A.unop)
    let φ : R.obj A.unop ⟶ R.obj (R.obj A.unop) := η.app (R.obj A.unop)
    have ht := (CochainComplex.IsKInjective.quasiIso_iff φ).mp
        (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C
          (R.obj A.unop))
    have hi := HomotopyCategory.quotient_inverts_homotopyEquivalences
      C (ComplexShape.up ℤ) _ ht
    -- Local instance justification (proof-local temporary data): map this actual homotopy equivalence through the displayed functors and then take its opposite.
    letI := hi
    change IsIso ((G.map (FH.map (q.map (η.app (R.obj A.unop))))).op)
    infer_instance
  have hα : (Functor.associator q.op L.op (T ⋙ G).op).hom ≫
      Functor.whiskerLeft q.op (NatTrans.op α) =
      Functor.LeftDerived.Deformation.counit (q ⋙ L).op R.op (NatTrans.op η)
        ((q ⋙ FH) ⋙ G).op (T ⋙ G).op (NatIso.op e.symm) := by
    ext A
    apply Quiver.Hom.unop_inj
    change (G.map ((Functor.KInjectiveModel.Homotopy.unit F).app (q.obj A.unop)) ≫
        𝟙 _) ≫ 𝟙 _ =
      (𝟙 _ ≫ G.map ((q ⋙ FH).map (η.app A.unop))) ≫ e.inv.app A.unop
    simp only [e, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id]
    rw [← G.map_comp]
    apply congrArg (fun a ↦ G.map a)
    change (Functor.KInjectiveModel.Homotopy.unitOnCochains F).app A.unop = _
    change (Functor.Homotopy.cochainIso F).hom.app A.unop ≫
        (𝟙 _ ≫ (Functor.KInjectiveModel.ordinaryCochain F).map (η.app A.unop) ≫
          (Functor.KInjectiveModel.fac F).inv.app A.unop) ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop) ≫ 𝟙 _ =
      (q ⋙ FH).map (η.app A.unop) ≫
        ((Functor.Homotopy.cochainIso F).hom.app (R.obj A.unop) ≫
          (Functor.KInjectiveModel.fac F).inv.app A.unop) ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop)
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    exact ((Functor.Homotopy.cochainIso F).hom.naturality_assoc
      (η.app A.unop) ((Functor.KInjectiveModel.fac F).inv.app A.unop ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop))).symm
  let w := Functor.LeftDerived.Deformation.terminalWitness (q ⋙ L).op U.op
    R.op (NatTrans.op η) hη ((q ⋙ FH) ⋙ G).op (T ⋙ G).op (NatIso.op e.symm) hAug
  let w' := Functor.LeftDerived.Deformation.terminalWitnessOfPrecomp q.op
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)).op
    L.op (FH ⋙ G).op (T ⋙ G).op (NatTrans.op α) (hα.symm ▸ w)
  exact ⟨⟨⟨dualWitness L (FH ⋙ G) (T ⋙ G) (NatTrans.op α) w'⟩⟩⟩

/-- Any specified right-derived model inherits the actual postcomposed K-injective witness. -/
private theorem right_postcompose {H : Type h} [Category.{vH} H]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (β : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (G : DerivedCategory D ⥤ H) :
    (RF ⋙ G).IsRightDerivedFunctor (Functor.whiskerRight β G ≫
      (Functor.associator DerivedCategory.Qh RF G).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let T := Functor.KInjectiveModel.derived F
  let α := Functor.KInjectiveModel.Homotopy.unit F
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let e := Functor.rightDerivedUnique (RF := T) (RF' := RF) (α := α) (α'₂ := β) (W := W)
  apply (Functor.isRightDerivedFunctor_iff_of_iso (RF := T ⋙ G) (RF' := RF ⋙ G)
    (α := Functor.whiskerRight α G ≫ (Functor.associator _ T G).hom)
    (α' := Functor.whiskerRight β G ≫ (Functor.associator _ RF G).hom)
    (W := W) (e := Functor.isoWhiskerRight e G) ?_).mp (rightModel_postcompose F G)
  ext K
  have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac T RF α β W (𝟙 _)) K
  change (G.map (α.app K) ≫ 𝟙 _) ≫ G.map (e.hom.app (DerivedCategory.Qh.obj K)) =
    G.map (β.app K) ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id, ← G.map_comp]
  exact congrArg (fun a ↦ G.map a) (h.trans (Category.id_comp _))

end RightModel
section ExactModel

universe uC vC uD vD h vH

/-- An invertible localization comparison supplies explicit terminal extension maps. -/
private theorem leftOfIso {C : Type uC} {D : Type uD} {H : Type h}
    [Category.{vC} C] [Category.{vD} D] [Category.{vH} H]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F : C ⥤ H) (T : D ⥤ H) (e : L ⋙ T ≅ F) :
    T.IsLeftDerivedFunctor e.hom W := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W H
  refine ⟨⟨⟨IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk (ff.preimage (E.hom ≫ e.inv)) ?_)
    (fun E φ ↦ ?_)⟩⟩⟩
  · change ((whiskeringLeft _ _ _).obj L).map
      (ff.preimage (E.hom ≫ e.inv)) ≫ e.hom = E.hom
    rw [ff.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · apply CostructuredArrow.hom_ext
    apply ff.map_injective
    change whiskerLeft L φ.left = ((whiskeringLeft _ _ _).obj L).map
      (ff.preimage (E.hom ≫ e.inv))
    rw [ff.map_preimage]
    apply (cancel_mono e.hom).1
    have hφ : whiskerLeft L φ.left ≫ e.hom = E.hom := CostructuredArrow.w φ
    exact hφ.trans (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end ExactModel

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The total augmentation's inverse image is additive by its actual module adjunction. -/
private theorem pullbackAdditive : (modulePullback a).Additive :=
  @RingedSite.ToposHom.modulePullback_additive _ _ _ _
    (spacesEtaleAugmentationRinged U a) (restrictScalars_structureMap_isRightAdjoint a)

/-- Quasi-coherent modules on the total étale site of an fppf hypercovering form a weak Serre class. -/
theorem quasiCoherent_isWeakSerreClass (ha : IsFppfHypercovering a) :
    (quasiCoherentModuleProperty U).IsWeakSerreClass := sorry

/-- Inverse image along an fppf hypercovering is exact on native module sheaves. -/
theorem pullback_exact (ha : IsFppfHypercovering a) :
    exactFunctor (RingedSite.ModuleCat.{u} (spacesRingedSite X))
      (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) (modulePullback a) := sorry

/-- Exact inverse image on the module categories of the total étale augmentation. -/
def exactPullback (ha : IsFppfHypercovering a) :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤ₑ
      RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  ⟨modulePullback a, pullback_exact a ha⟩

/-- The exact native derived action of inverse image along the total étale augmentation. -/
def ambientPullback (ha : IsFppfHypercovering a) :
    RingedSite.NativeDerived.category.{u} (spacesRingedSite X) ⥤
      RingedSite.NativeDerived.category.{u} (etaleTotalRingedSite U) := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  exact (exactPullback a ha).mapDerivedCategory

/-- The canonical unbounded right-derived direct image along the total étale augmentation. -/
abbrev ambientPushforward := EtaleModuleDerived.pushforward a

/-- The native homotopy localization comparison for exact inverse image. -/
private def pullbackFactors (ha : IsFppfHypercovering a) :
    RingedSite.NativeDerived.localization.{u} (spacesRingedSite X) ⋙ ambientPullback a ha ≅
      (@Functor.mapHomotopyCategory _ _ _ _ _ _ _ (modulePullback a)
        (pullbackAdditive a) (ComplexShape.up ℤ)) ⋙
        RingedSite.NativeDerived.localization.{u} (etaleTotalRingedSite U) := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  exact (exactPullback a ha).obj.mapDerivedCategoryFactorsh

/-- The exact native inverse image has the displayed terminal extension witness. -/
theorem ambientPullback_isLeftDerived (ha : IsFppfHypercovering a) :
    (ambientPullback a ha).IsLeftDerivedFunctor
      (@Functor.mapDerivedCategoryFactorsh _ _
        (RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X))
        (RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)) _ _
        (RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U))
        (RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U))
        (exactPullback a ha).obj inferInstance
        (exactPullback a ha).property.1 (exactPullback a ha).property.2).hom
      (RingedSite.NativeDerived.quasiIso.{u} (spacesRingedSite X)) := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  exact leftOfIso _ _ _ _ (pullbackFactors a ha)

/-- Postcomposition of exact inverse image retains its explicit terminal extension maps. -/
theorem ambientPullbackPushforward_isLeftDerived (ha : IsFppfHypercovering a) :
    (ambientPullback a ha ⋙ ambientPushforward a).IsLeftDerivedFunctor
      ((Functor.associator (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X))
        (ambientPullback a ha) (ambientPushforward a)).inv ≫
          Functor.whiskerRight (@Functor.mapDerivedCategoryFactorsh _ _
        (RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X))
        (RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)) _ _
        (RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U))
        (RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U))
        (exactPullback a ha).obj inferInstance
        (exactPullback a ha).property.1 (exactPullback a ha).property.2).hom (ambientPushforward a))
      (RingedSite.NativeDerived.quasiIso.{u} (spacesRingedSite X)) := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  exact leftOfIso _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackFactors a ha) (ambientPushforward a))

/-- Postcomposition of derived direct image retains its actual K-injective initial maps. -/
theorem ambientPushforwardPullback_isRightDerived (ha : IsFppfHypercovering a) :
    (ambientPushforward a ⋙ ambientPullback a ha).IsRightDerivedFunctor
      (Functor.whiskerRight (EtaleModuleDerived.pushforwardUnit a) (ambientPullback a ha) ≫
        (Functor.associator (RingedSite.NativeDerived.localization.{u} (etaleTotalRingedSite U))
          (ambientPushforward a) (ambientPullback a ha)).hom)
      (RingedSite.NativeDerived.quasiIso.{u} (etaleTotalRingedSite U)) := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  -- Local instance justification (proof-local temporary data): the actual canonical total-right-derived model supplies this particular native unit certificate.
  letI : (ambientPushforward a).IsRightDerivedFunctor (EtaleModuleDerived.pushforwardUnit a)
      (RingedSite.NativeDerived.quasiIso.{u} (etaleTotalRingedSite U)) :=
    by
      dsimp only [ambientPushforward, EtaleModuleDerived.pushforward,
        EtaleModuleDerived.pushforwardUnit, RingedSite.ToposHom.NativeDerived.pushforward]
      infer_instance
  -- Local instance justification (defeq pin): the postcomposed K-injective witness requires the explicit direct-image additive certificate for these native abelian structures.
  letI := EtaleModuleDerived.pushforward_additive a
  exact right_postcompose (modulePushforward a) (ambientPushforward a)
    (EtaleModuleDerived.pushforwardUnit a) (ambientPullback a ha)

/-- The actual native derived inverse-image/direct-image adjunction of the total augmentation. -/
def ambientAdjunction (ha : IsFppfHypercovering a) :
    ambientPullback a ha ⊣ ambientPushforward a := by
  -- Local instance justification (defeq pin): use native addition on the base module category in the standard derived-category construction.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): use the same native addition on the total site.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the base category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the total category's native localization.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  -- Local instance justification (proof-local temporary data): the chosen exact action carries the explicit localization terminal witness used in this derived adjunction.
  letI := ambientPullback_isLeftDerived a ha
  -- Local instance justification (proof-local temporary data): retain the postcomposed terminal witness of the same exact comparison.
  letI := ambientPullbackPushforward_isLeftDerived a ha
  -- Local instance justification (proof-local temporary data): retain the postcomposed K-injective initial witness and its actual direct-image unit.
  letI := ambientPushforwardPullback_isRightDerived a ha
  -- Local instance justification (proof-local temporary data): use the canonical native total-derived unit, whose existence stores the actual K-injective model witness.
  letI : (ambientPushforward a).IsRightDerivedFunctor (EtaleModuleDerived.pushforwardUnit a)
      (RingedSite.NativeDerived.quasiIso.{u} (etaleTotalRingedSite U)) :=
    by
      dsimp only [ambientPushforward, EtaleModuleDerived.pushforward,
        EtaleModuleDerived.pushforwardUnit, RingedSite.ToposHom.NativeDerived.pushforward]
      infer_instance
  exact (@Adjunction.mapHomotopyCategoryAdjunction _ _ _ _ _ _ _ _
    (pullbackAdditive a) (EtaleModuleDerived.pushforward_additive a) (moduleAdjunction a)).derived
    (RingedSite.NativeDerived.quasiIso.{u} (spacesRingedSite X))
    (RingedSite.NativeDerived.quasiIso.{u} (etaleTotalRingedSite U))
    (@Functor.mapDerivedCategoryFactorsh _ _
      (RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X))
      (RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)) _ _
      (RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U))
      (RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U))
      (exactPullback a ha).obj inferInstance
      (exactPullback a ha).property.1 (exactPullback a ha).property.2).hom
    (EtaleModuleDerived.pushforwardUnit a)

/-- Exact derived inverse image preserves quasi-coherent homology in every integer degree. -/
theorem pullback_le_inverseImage (ha : IsFppfHypercovering a) :
    baseProperty X ≤ (totalProperty U).inverseImage (ambientPullback a ha) := sorry

/-- Unbounded derived direct image along an fppf hypercovering preserves quasi-coherent homology. -/
theorem pushforward_le_inverseImage (ha : IsFppfHypercovering a) :
    totalProperty U ≤ (baseProperty X).inverseImage (ambientPushforward a) := sorry

/-- Exact inverse image restricted to the unbounded quasi-coherent derived categories. -/
def pullback (ha : IsFppfHypercovering a) : Base X ⥤ Total U :=
  FullSubcategory.restrict (ambientPullback a ha) (pullback_le_inverseImage a ha)

/-- The underlying derived object of restricted inverse image is the exact ambient action. -/
theorem pullback_obj (ha : IsFppfHypercovering a) (E : Base X) :
    ((pullback a ha).obj E).obj = (ambientPullback a ha).obj E.obj := rfl

/-- Canonical unbounded derived direct image restricted to quasi-coherent homology. -/
def pushforward (ha : IsFppfHypercovering a) : Total U ⥤ Base X :=
  FullSubcategory.restrict (ambientPushforward a) (pushforward_le_inverseImage a ha)

/-- The underlying restricted direct image is the canonical total derived direct image. -/
theorem pushforward_obj (ha : IsFppfHypercovering a) (E : Total U) :
    ((pushforward a ha).obj E).obj = (EtaleModuleDerived.pushforward a).obj E.obj := rfl

/-- The native ambient adjunction restricts with the same actual unit and counit components. -/
def adjunction (ha : IsFppfHypercovering a) : pullback a ha ⊣ pushforward a ha where
  unit :=
    { app E := ObjectProperty.homMk ((ambientAdjunction a ha).unit.app E.obj)
      naturality := fun _ _ f ↦ ObjectProperty.hom_ext _
        ((ambientAdjunction a ha).unit.naturality f.hom) }
  counit :=
    { app E := ObjectProperty.homMk ((ambientAdjunction a ha).counit.app E.obj)
      naturality := fun _ _ f ↦ ObjectProperty.hom_ext _
        ((ambientAdjunction a ha).counit.naturality f.hom) }
  left_triangle_components := fun E ↦ ObjectProperty.hom_ext _
    ((ambientAdjunction a ha).left_triangle_components E.obj)
  right_triangle_components := fun E ↦ ObjectProperty.hom_ext _
    ((ambientAdjunction a ha).right_triangle_components E.obj)

/-- The restricted unit is precisely the actual ambient derived-adjunction unit. -/
theorem adjunction_unit_app_hom (ha : IsFppfHypercovering a) (E : Base X) :
    ((adjunction a ha).unit.app E).hom = (ambientAdjunction a ha).unit.app E.obj := rfl

/-- The restricted counit is precisely the actual ambient derived-adjunction counit. -/
theorem adjunction_counit_app_hom (ha : IsFppfHypercovering a) (E : Total U) :
    ((adjunction a ha).counit.app E).hom = (ambientAdjunction a ha).counit.app E.obj := rfl

/-- The actual ambient derived-adjunction unit is invertible on quasi-coherent base objects. -/
theorem unit_app_isIso (ha : IsFppfHypercovering a) (E : Base X) :
    IsIso ((ambientAdjunction a ha).unit.app E.obj) := sorry

/-- The actual ambient derived-adjunction counit is invertible on quasi-coherent total objects. -/
theorem counit_app_isIso (ha : IsFppfHypercovering a) (E : Total U) :
    IsIso ((ambientAdjunction a ha).counit.app E.obj) := sorry

/-- Exact pullback along an fppf hypercovering is an equivalence on unbounded
derived categories with quasi-coherent homology, with restricted derived direct image as
the right adjoint. -/
instance pullback_isEquivalence (ha : IsFppfHypercovering a) :
    (pullback a ha).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial.QCohDerived
