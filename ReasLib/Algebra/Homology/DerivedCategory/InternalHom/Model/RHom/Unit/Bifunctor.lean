module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor.Model
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherent regular-source unit comparisons

This leaf combines an honest two-variable comparison for canonical module `RHom` with the
regular degree-zero unit API.  Its first layer accepts a separate pointwise closed comparison;
its second layer reconstructs that comparison from an explicit ambient tensor model.  Thus source
naturality comes from the bifunctor owner, while no tensor model is hidden in typeclass search.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [RHom.Has (A := A)]

/-- `0E1U:` Transport a canonical regular-source unit comparison through a coherent bifunctor
comparison, keeping the pointwise and coherent closed presentations explicit. -/
@[stacks 0E1U "coherent selected internal-Hom unit comparison"]
noncomputable def singleIhomTargetIsoOf
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  (M.targetIso (RHom.Unit.single (A := A))).symm ≪≫ RHom.Unit.targetIso N s

/-- The objectwise selected internal-Hom unit comparison obtained from coherent and pointwise
comparison data. -/
@[stacks 0E1U "coherent selected internal-Hom unit object comparison"]
noncomputable abbrev singleIhomObjIsoOf
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).obj K ≅ K :=
  (M.singleIhomTargetIsoOf N s).app K

/-- The selected internal-Hom unit comparison is natural in its target. -/
@[reassoc, stacks 0E1U "coherent selected unit target naturality"]
theorem singleIhomObjIsoOf_hom_naturality
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).map f ≫
        (M.singleIhomObjIsoOf N s L).hom =
      (M.singleIhomObjIsoOf N s K).hom ≫ f := by
  simpa using (M.singleIhomTargetIsoOf N s).hom.naturality f

/-- The inverse selected internal-Hom unit comparison is natural in its target. -/
@[reassoc, stacks 0E1U "inverse coherent selected unit target naturality"]
theorem singleIhomObjIsoOf_inv_naturality
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    f ≫ (M.singleIhomObjIsoOf N s L).inv =
      (M.singleIhomObjIsoOf N s K).inv ≫
        (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).map f := by
  simpa using (M.singleIhomTargetIsoOf N s).inv.naturality f

/-- The forward component of the coherent selected unit comparison is the inverse bifunctor
comparison followed by the canonical regular-source unit comparison. -/
@[simp, stacks 0E1U "coherent selected unit forward component from pointwise data"]
theorem singleIhomObjIsoOf_hom
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.singleIhomObjIsoOf N s K).hom =
      (M.objIso (RHom.Unit.single (A := A)) K).inv ≫
        (RHom.Unit.objIso N s K).hom := by
  simp [singleIhomObjIsoOf, singleIhomTargetIsoOf]

/-- The inverse component first applies the inverse canonical unit comparison and then the
coherent bifunctor comparison. -/
@[simp, stacks 0E1U "inverse coherent selected unit component from pointwise data"]
theorem singleIhomObjIsoOf_inv
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.singleIhomObjIsoOf N s K).inv =
      (RHom.Unit.objIso N s K).inv ≫
        (M.objIso (RHom.Unit.single (A := A)) K).hom := by
  simp [singleIhomObjIsoOf, singleIhomTargetIsoOf]

/-- The coherent canonical-`RHom` comparison transports regular-source precomposition to selected
internal-Hom precomposition. -/
@[reassoc, stacks 0E1U "regular-source coherent RHom source naturality"]
theorem singlePre_objIso_natural_source
    (M : RHom.BifunctorComparison (A := A))
    (a : A) (L : DerivedCategory (ModuleCat.{u} A)) :
    (RHom.Unit.singlePre (A := A) a).app L ≫
        (M.objIso (RHom.Unit.single (A := A)) L).hom =
      (M.objIso (RHom.Unit.single (A := A)) L).hom ≫
        (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app L := by
  simpa only [RHom.Unit.singlePre_app] using
    M.objIso_natural_source (RHom.Unit.singleMap a) L

/-- The inverse coherent comparison transports selected regular-source precomposition back to
canonical `RHom` precomposition. -/
@[reassoc, stacks 0E1U "inverse regular-source coherent RHom naturality"]
theorem singlePre_objIso_natural_source_inv
    (M : RHom.BifunctorComparison (A := A))
    (a : A) (L : DerivedCategory (ModuleCat.{u} A)) :
    (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app L ≫
        (M.objIso (RHom.Unit.single (A := A)) L).inv =
      (M.objIso (RHom.Unit.single (A := A)) L).inv ≫
        (RHom.Unit.singlePre (A := A) a).app L := by
  apply (cancel_mono (M.objIso (RHom.Unit.single (A := A)) L).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [M.singlePre_objIso_natural_source]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Canonical precomposition followed by the coherent fixed-source comparison is selected
internal-Hom precomposition after the comparison at the original source. -/
@[reassoc, stacks 0E1U "coherent RHom precomposition naturality"]
theorem pre_comp_targetIso_hom
    (M : RHom.BifunctorComparison (A := A))
    {X Y : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ Y) :
    RHom.pre (A := A) p ≫ (M.targetIso X).hom =
      (M.targetIso Y).hom ≫ MonoidalClosed.preOf M.closed p := by
  ext K
  simpa only [NatTrans.comp_app, RHom.pre_app, M.targetIso_hom_app] using
    M.objIso_natural_source p K

/-- Under the coherent selected unit comparison, precomposition by multiplication on the regular
degree-zero object is scalar multiplication on the target. -/
@[reassoc, stacks 0E1U "coherent selected unit scalar comparison"]
theorem singleMap_pre_singleIhomObjIsoOf_hom
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (a : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app K ≫
        (M.singleIhomObjIsoOf N s K).hom =
      (M.singleIhomObjIsoOf N s K).hom ≫ (a • 𝟙 K) := by
  rw [M.singleIhomObjIsoOf_hom]
  rw [← Category.assoc, M.singlePre_objIso_natural_source_inv, Category.assoc,
    RHom.Unit.singlePre_objIso_hom]
  rw [Category.assoc]

/-- The inverse selected unit comparison transports scalar multiplication back to regular-source
precomposition. -/
@[reassoc, stacks 0E1U "inverse coherent selected unit scalar comparison"]
theorem singleMap_pre_singleIhomObjIsoOf_inv
    (M : RHom.BifunctorComparison (A := A))
    (N : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (a : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (a • 𝟙 K) ≫ (M.singleIhomObjIsoOf N s K).inv =
      (M.singleIhomObjIsoOf N s K).inv ≫
        (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app K := by
  apply (cancel_mono (M.singleIhomObjIsoOf N s K).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [M.singleMap_pre_singleIhomObjIsoOf_hom]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

section Model

variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- `0E1U:` The selected internal-Hom unit comparison determined by one coherent bifunctor
comparison, an explicit ambient tensor model, and a regular-object unit comparison. -/
@[stacks 0E1U "selected unit comparison from a coherent RHom model"]
noncomputable def singleIhomTargetIso
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  RHom.Unit.ihomTargetIso (M.toClosedComparison T) s

/-- The objectwise selected internal-Hom unit comparison determined by the coherent gate. -/
@[stacks 0E1U "selected unit object comparison from a coherent RHom model"]
noncomputable abbrev singleIhomObjIso
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).obj K ≅ K :=
  (M.singleIhomTargetIso T s).app K

/-- The model-derived unit comparison is the selected unit comparison of its recovered pointwise
gate. -/
@[simp, stacks 0E1U "model-derived coherent unit comparison formula"]
theorem singleIhomTargetIso_eq_unit
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    M.singleIhomTargetIso T s = RHom.Unit.ihomTargetIso (M.toClosedComparison T) s := rfl

/-- The inverse model-derived selected unit comparison first applies the inverse canonical unit
comparison and then the coherent canonical-to-selected comparison. -/
@[simp, stacks 0E1U "inverse coherent selected unit comparison formula"]
theorem singleIhomTargetIso_inv
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    (M.singleIhomTargetIso T s).inv =
      (RHom.Unit.targetIso (M.toClosedComparison T) s).inv ≫
        (M.targetIso (RHom.Unit.single (A := A))).hom := by
  simp [singleIhomTargetIso, RHom.Unit.ihomTargetIso]

/-- The model-derived unit comparison is the intrinsic selected internal-Hom/unit comparison
transported along the regular-object unit isomorphism. -/
@[stacks 0E1U "coherent unit comparison is intrinsic"]
theorem singleIhomTargetIso_eq_ihomUnitIsoOf
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    M.singleIhomTargetIso T s = MonoidalClosed.ihomUnitIsoOf M.closed s := by
  let U := RHom.Unit.single (A := A)
  let baseAdj := (RightInternalHom.ofBraidedClosedOf M.closed).adj₂.adj U
  let t := T.tensorRightIsoFunctor U
  let e₀ := ((curriedTensor (DerivedCategory (ModuleCat.{u} A))).flip.mapIso s) ≪≫
    rightUnitorNatIso (DerivedCategory (ModuleCat.{u} A))
  let e := RHom.Unit.tensorUnitComparisonOf T s
  let adjH := DerivedTensor.Right.Closed.adjunctionOf M.closed T U
  let adjR := adjH.ofNatIsoRight (M.targetIso U).symm
  have htransport := Adjunction.rightAdjointUniq_ofNatIsoRight_ofNatIsoLeft
    adjH (M.targetIso U).symm e
  have hselected :
      M.singleIhomTargetIso T s =
        (adjH.ofNatIsoLeft e).rightAdjointUniq Adjunction.id := by
    apply Iso.ext
    ext K
    simp only [singleIhomTargetIso, RHom.Unit.ihomTargetIso, Iso.trans_hom,
      NatTrans.comp_app]
    rw [M.toClosedComparison_targetIso]
    change (M.targetIso U).inv.app K ≫
        ((adjR.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app K = _
    change (M.targetIso U).symm.hom.app K ≫
        ((adjR.ofNatIsoLeft e).rightAdjointUniq Adjunction.id).hom.app K = _
    rw [← NatTrans.congr_app htransport K]
    rw [Adjunction.rightAdjointUniq_trans_app]
  rw [hselected]
  change (((baseAdj.ofNatIsoLeft t).ofNatIsoLeft e).rightAdjointUniq
    Adjunction.id) = _
  rw [Adjunction.rightAdjointUniq_ofNatIsoLeft_trans]
  have hte : t ≪≫ e = e₀ := by
    apply Iso.ext
    ext K
    simp [U, t, e, e₀, RHom.Unit.tensorUnitComparisonOf,
      DerivedTensor.Right.Monoidal.Model.functorIsoUnit,
      DerivedTensor.Right.Monoidal.Model.tensorRightIsoFunctor, Iso.trans_hom]
  rw [hte]
  exact MonoidalClosed.rightAdjointUniq_ofBraidedClosedOf_unit M.closed s

/-- Objectwise, the model-derived unit comparison is the intrinsic selected internal-Hom/unit
comparison. -/
@[stacks 0E1U "coherent unit object comparison is intrinsic"]
theorem singleIhomObjIso_eq_ihomUnitIsoOf_app
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    M.singleIhomObjIso T s K = (MonoidalClosed.ihomUnitIsoOf M.closed s).app K := by
  rw [← M.singleIhomTargetIso_eq_ihomUnitIsoOf T s]

/-- The forward component is the inverse coherent canonical-`RHom` comparison followed by the
canonical regular-source unit comparison. -/
@[simp, stacks 0E1U "coherent selected unit forward component"]
theorem singleIhomObjIso_hom
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.singleIhomObjIso T s K).hom =
      (M.objIso (RHom.Unit.single (A := A)) K).inv ≫
        (RHom.Unit.objIso (M.toClosedComparison T) s K).hom := by
  simp [singleIhomObjIso, singleIhomTargetIso, RHom.Unit.ihomTargetIso]

/-- The inverse component is the inverse canonical unit comparison followed by the coherent
canonical-`RHom` comparison. -/
@[simp, stacks 0E1U "coherent selected unit inverse component"]
theorem singleIhomObjIso_inv
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.singleIhomObjIso T s K).inv =
      (RHom.Unit.objIso (M.toClosedComparison T) s K).inv ≫
        (M.objIso (RHom.Unit.single (A := A)) K).hom := by
  simp [singleIhomObjIso, singleIhomTargetIso, RHom.Unit.ihomTargetIso]

/-- The model-derived selected internal-Hom unit comparison is natural in the target. -/
@[reassoc, stacks 0E1U "coherent selected unit naturality"]
theorem singleIhomObjIso_hom_naturality
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).map f ≫
        (M.singleIhomObjIso T s L).hom =
      (M.singleIhomObjIso T s K).hom ≫ f := by
  simpa using (M.singleIhomTargetIso T s).hom.naturality f

/-- The inverse model-derived selected internal-Hom unit comparison is natural in the target. -/
@[reassoc, stacks 0E1U "inverse coherent selected unit naturality"]
theorem singleIhomObjIso_inv_naturality
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    f ≫ (M.singleIhomObjIso T s L).inv =
      (M.singleIhomObjIso T s K).inv ≫
        (MonoidalClosed.ihomOf M.closed (RHom.Unit.single (A := A))).map f := by
  simpa using (M.singleIhomTargetIso T s).inv.naturality f

/-- Under the model-derived unit comparison, regular-source multiplication acts by scalars on
the target. -/
@[reassoc, stacks 0E1U "model-derived selected unit scalar comparison"]
theorem singleMap_pre_singleIhomObjIso_hom
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (a : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app K ≫
        (M.singleIhomObjIso T s K).hom =
      (M.singleIhomObjIso T s K).hom ≫ (a • 𝟙 K) := by
  rw [M.singleIhomObjIso_hom]
  rw [← Category.assoc, M.singlePre_objIso_natural_source_inv, Category.assoc,
    RHom.Unit.singlePre_objIso_hom]
  rw [Category.assoc]

/-- The inverse model-derived unit comparison transports scalar multiplication back to
regular-source precomposition. -/
@[reassoc, stacks 0E1U "inverse model-derived selected unit scalar comparison"]
theorem singleMap_pre_singleIhomObjIso_inv
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (a : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (a • 𝟙 K) ≫ (M.singleIhomObjIso T s K).inv =
      (M.singleIhomObjIso T s K).inv ≫
        (MonoidalClosed.preOf M.closed (RHom.Unit.singleMap a)).app K := by
  apply (cancel_mono (M.singleIhomObjIso T s K).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [M.singleMap_pre_singleIhomObjIso_hom]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `0E1U:` The natural transformation from the identity to a selected internal Hom induced by a
map from its source to the regular degree-zero object. -/
@[stacks 0E1U "coherent regular-source selected internal-Hom unit"]
noncomputable def unitOfPre
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A)) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶ MonoidalClosed.ihomOf M.closed X :=
  MonoidalClosed.unitOfPre M.closed (M.singleIhomTargetIso T s) p

/-- The coherent regular-source wrapper is the generic selected internal-Hom construction for its
explicitly built unit comparison. -/
@[simp, stacks 0E1U "coherent selected unit generic formula"]
theorem unitOfPre_eq_monoidalClosed
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A)) :
    M.unitOfPre T s p =
      MonoidalClosed.unitOfPre M.closed (M.singleIhomTargetIso T s) p := rfl

/-- The coherent regular-source unit is the intrinsic selected-Hom construction from the same
regular-object unit isomorphism. -/
@[stacks 0E1U "coherent selected unit intrinsic formula"]
theorem unitOfPre_eq_unitOfPreOfIsoUnit
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A)) :
    M.unitOfPre T s p = MonoidalClosed.unitOfPreOfIsoUnit M.closed s p := by
  unfold unitOfPre MonoidalClosed.unitOfPreOfIsoUnit
  rw [M.singleIhomTargetIso_eq_ihomUnitIsoOf]

/-- Objectwise, the selected unit is the inverse unit comparison followed by internal-Hom
precomposition. -/
@[simp, stacks 0E1U "coherent selected unit component"]
theorem unitOfPre_app
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.unitOfPre T s p).app K =
      (M.singleIhomObjIso T s K).inv ≫ (MonoidalClosed.preOf M.closed p).app K := by
  simpa using MonoidalClosed.unitOfPre_app M.closed (M.singleIhomTargetIso T s) p K

/-- The selected internal-Hom unit induced by precomposition is natural in its target. -/
@[reassoc, stacks 0E1U "coherent selected unit target naturality"]
theorem unitOfPre_naturality
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X K L : DerivedCategory (ModuleCat.{u} A)}
    (p : X ⟶ RHom.Unit.single (A := A)) (f : K ⟶ L) :
    f ≫ (M.unitOfPre T s p).app L =
      (M.unitOfPre T s p).app K ≫ (MonoidalClosed.ihomOf M.closed X).map f := by
  simpa using MonoidalClosed.unitOfPre_naturality
    M.closed (M.singleIhomTargetIso T s) p f

/-- Precomposing the source map composes the coherent selected unit with internal-Hom
precomposition. -/
@[stacks 0E1U "coherent selected unit source composition"]
theorem unitOfPre_comp
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X Y : DerivedCategory (ModuleCat.{u} A)}
    (p : X ⟶ RHom.Unit.single (A := A)) (q : Y ⟶ X) :
    M.unitOfPre T s (q ≫ p) =
      M.unitOfPre T s p ≫ MonoidalClosed.preOf M.closed q := by
  simpa using MonoidalClosed.unitOfPre_comp
    M.closed (M.singleIhomTargetIso T s) p q

/-- The coherent selected unit induced by the identity is the inverse regular-source unit
comparison. -/
@[simp, stacks 0E1U "coherent selected unit identity"]
theorem unitOfPre_id
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    M.unitOfPre T s (𝟙 (RHom.Unit.single (A := A))) =
      (M.singleIhomTargetIso T s).inv := by
  simpa using MonoidalClosed.unitOfPre_id M.closed
    (RHom.Unit.single (A := A)) (M.singleIhomTargetIso T s)

/-- The coherent selected unit induced by regular multiplication is scalar multiplication followed
by the inverse regular-source unit comparison. -/
@[simp, stacks 0E1U "coherent selected unit scalar component"]
theorem unitOfPre_singleMap_app
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (a : A) (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.unitOfPre T s (RHom.Unit.singleMap a)).app K =
      (a • 𝟙 K) ≫ (M.singleIhomObjIso T s K).inv := by
  rw [M.unitOfPre_app, ← M.singleMap_pre_singleIhomObjIso_inv]

/-- The selected unit is the canonical `RHom` unit transported through the coherent fixed-source
comparison. -/
@[stacks 0E1U "coherent selected unit agrees with canonical RHom"]
theorem unitOfPre_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A)) :
    M.unitOfPre T s p =
      RHom.Unit.unitOfPre (M.toClosedComparison T) s p ≫ (M.targetIso X).hom := by
  ext K
  rw [unitOfPre_app, NatTrans.comp_app, RHom.Unit.unitOfPre_app,
    singleIhomObjIso_inv]
  simp only [Category.assoc]
  rw [← M.objIso_natural_source p K, RHom.pre_app]
  rw [M.targetIso_hom_app]
  exact (Category.assoc _ _ _).symm

/-- Objectwise, the selected unit is the canonical `RHom` unit followed by the coherent
canonical-to-selected comparison. -/
@[simp, stacks 0E1U "coherent selected unit component agrees with canonical RHom"]
theorem unitOfPre_app_eq_canonical
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {X : DerivedCategory (ModuleCat.{u} A)} (p : X ⟶ RHom.Unit.single (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.unitOfPre T s p).app K =
      (RHom.Unit.unitOfPre (M.toClosedComparison T) s p).app K ≫
        (M.objIso X K).hom := by
  simpa only [NatTrans.comp_app, M.targetIso_hom_app] using
    congrArg (fun q ↦ q.app K) (M.unitOfPre_eq_canonical T s p)

end Model

end CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison
