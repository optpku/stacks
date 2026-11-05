/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactificationChange
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Compactification
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualCurveRefinement

/-- Use the regular affine-neighbourhood witness itself, so this construction does not
rely on the unproved neighbourhood wrapper. -/
private theorem stalk_regularLocalRing (X : Scheme.{u}) [Scheme.Regular X] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have hX : Scheme.Regular X := inferInstance
  obtain ⟨U, hxU, hU⟩ := hX.out x
  letI : IsRegularRing Γ(X, (U : X.Opens)) := hU
  letI : Algebra Γ(X, (U : X.Opens)) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let p := U.2.primeIdealOf ⟨x, hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The stalks of a regular curve are valuation rings, including at the generic point. -/
private theorem stalk_valuationRing {k : Type u} [Field k]
    (C : SchemeOverField k) [Curve C] [Scheme.Regular C.left] (x : C.left) :
    ValuationRing (C.left.presheaf.stalk x) := by
  letI := stalk_regularLocalRing C.left x
  have hdim : ringKrullDim (C.left.presheaf.stalk x) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (C.left.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le.trans
      (Curve.topologicalKrullDim_eq_one (X := C)).le
  have hfin : Module.finrank (IsLocalRing.ResidueField (C.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)) ≤ 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace
      (C.left.presheaf.stalk x)).mp inferInstance
    rw [← h] at hdim
    exact_mod_cast hdim
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (C.left.presheaf.stalk x)).out 5 1).mp hfin

/-- Restriction from a stalk to the function field agrees with the given partial map. -/
private theorem partialMap_fromFunctionField {X Y : Scheme.{u}} [IsIntegral X]
    (f : X.PartialMap Y) {x : X} (hx : x ∈ f.domain) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        f.fromSpecStalkOfMem hx = f.fromFunctionField := by
  unfold Scheme.PartialMap.fromSpecStalkOfMem Scheme.PartialMap.fromFunctionField
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono f.domain.ι).mp
  simp only [Category.assoc, Opens.fromSpecStalkOfMem_ι]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes trivial)

set_option backward.isDefEq.respectTransparency false in
/-- Properness extends a partial map at every valuation stalk; the maximal-domain
representative supplied by mathlib then glues these extensions. -/
private theorem exists_hom_of_partialMap
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [IsIntegral X]
    [S.IsSeparated] [Y.IsSeparated] [IsProper (Y ↘ S)]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (f : X.PartialMap Y) [f.IsOver S] :
    ∃ g : X ⟶ Y, g.IsOver S ∧ f.domain.ι ≫ g = f.hom := by
  let φ := f.toRationalMap
  have hf : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) :=
    (inferInstance : f.IsOver S).1
  have hdom : φ.domain = ⊤ := by
    apply top_le_iff.mp
    intro x _
    letI := hX x
    letI : IsDomain (X.presheaf.stalk x) :=
      Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
    have hval : ValuativeCriterion (Y ↘ S) := by
      have h : IsProper (Y ↘ S) := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1
    let sq : ValuativeCommSq (Y ↘ S) :=
      { R := X.presheaf.stalk x
        commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
        domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
        valuationRing := hX x
        K := X.functionField
        field := inferInstanceAs (Field X.functionField)
        algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
        isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
        i₁ := f.fromFunctionField
        i₂ := X.fromSpecStalk x ≫ (X ↘ S)
        commSq := ⟨by
          change f.fromFunctionField ≫ (Y ↘ S) =
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
              (X.fromSpecStalk x ≫ (X ↘ S))
          change f.fromFunctionField ≫ (Y ↘ S) =
            Spec.map (X.presheaf.stalkSpecializes
              ((genericPoint_spec X).specializes trivial)) ≫
              (X.fromSpecStalk x ≫ (X ↘ S))
          rw [← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
          simp only [Scheme.PartialMap.fromFunctionField,
            Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc,
            hf, Opens.fromSpecStalkOfMem_ι_assoc]⟩ }
    letI := (ValuativeCriterion.existence hval) sq
    let g := Scheme.PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) (x := x)
      sq.commSq.lift sq.commSq.fac_right
    have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    have hgf : g.toRationalMap = φ := by
      apply Scheme.RationalMap.eq_of_fromFunctionField_eq
      change g.fromFunctionField = f.fromFunctionField
      rw [← partialMap_fromFunctionField g hxg,
        Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
      exact sq.commSq.fac_left
    exact Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, hgf⟩
  letI : IsIso φ.toPartialMap.domain.ι := by
    change IsIso φ.domain.ι
    rw [hdom]
    change IsIso X.topIso.hom
    infer_instance
  let g := inv φ.toPartialMap.domain.ι ≫ φ.toPartialMap.hom
  refine ⟨g, ?_, ?_⟩
  · constructor
    have hφ : φ.toPartialMap.hom ≫ (Y ↘ S) = φ.toPartialMap.domain.ι ≫ (X ↘ S) :=
      (inferInstance : φ.toPartialMap.IsOver S).1
    change (inv φ.toPartialMap.domain.ι ≫ φ.toPartialMap.hom) ≫ (Y ↘ S) = X ↘ S
    rw [Category.assoc, hφ, IsIso.inv_hom_id_assoc]
  · have hle : f.domain ≤ φ.toPartialMap.domain := f.le_domain_toRationalMap
    have h := f.toPartialMap_toRationalMap_restrict
    change X.homOfLE hle ≫ φ.toPartialMap.hom = f.hom at h
    rw [← h]
    dsimp only [g]
    rw [← Category.assoc]
    congr 1
    apply (cancel_mono φ.toPartialMap.domain.ι).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (X.homOfLE_ι hle).symm

/-- Extending to a proper target only needs a regular source curve, with no
projectivity assumption on that source. -/
theorem extension_existsUnique_of_regular {k : Type u} [Field k]
    (U C : SchemeOverField k) [Curve U] [Curve C]
    [Scheme.Regular C.left]
    (j : U ⟶ C) [IsOpenImmersion j.left]
    (P : Compactification.Of (Spec (CommRingCat.of k)) U) :
    ∃! f : C ⟶ P.obj.right, j ≫ f = P.obj.hom := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩
  letI : P.obj.right.left.Over (Spec (CommRingCat.of k)) := ⟨P.obj.right.hom⟩
  letI : IsProper (P.obj.right.left ↘ Spec (CommRingCat.of k)) := by
    change IsProper P.obj.right.hom
    exact P.property.isProper
  letI : IsDominant j.left :=
    ⟨j.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  let f : C.left.PartialMap P.obj.right.left :=
    { domain := j.left.opensRange
      dense_domain := j.left.denseRange
      hom := j.left.isoOpensRange.inv ≫ Compactification.Of.ι P }
  letI : f.IsOver (Spec (CommRingCat.of k)) := by
    constructor
    change (j.left.isoOpensRange.inv ≫ P.obj.hom.left) ≫ P.obj.right.hom =
      j.left.opensRange.ι ≫ C.hom
    rw [Category.assoc, Over.w P.obj.hom, ← Over.w j,
      ← Category.assoc, j.left.isoOpensRange_inv_comp]
  letI : P.obj.right.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from P.obj.right.hom]
    infer_instance⟩
  obtain ⟨g, hg, hres⟩ := exists_hom_of_partialMap (S := Spec (CommRingCat.of k))
    (fun x ↦ stalk_valuationRing C x) f
  let F : C ⟶ P.obj.right := Over.homMk g (hg.1)
  have hF : j ≫ F = P.obj.hom := by
    apply Over.OverMorphism.ext
    change j.left ≫ g = Compactification.Of.ι P
    change j.left.opensRange.ι ≫ g = j.left.isoOpensRange.inv ≫ Compactification.Of.ι P at hres
    rw [← j.left.isoOpensRange_inv_comp, Category.assoc] at hres
    have h := congrArg (fun e ↦ j.left.isoOpensRange.hom ≫ e) hres
    simpa only [Iso.hom_inv_id_assoc] using h
  refine ⟨F, hF, fun H hH ↦ ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated P.obj.right.hom
    ((Over.w H).trans (Over.w F).symm) j.left
  exact (congrArg (fun e ↦ e.left) hH).trans
    (congrArg (fun e ↦ e.left) hF).symm

variable {k : Type u} [Field k]
variable (U C : SchemeOverField k) [Curve U] [Curve C]
variable [hregular : Scheme.Regular C.left] [hprojective : Projective C.hom]
variable (j : U ⟶ C) [hopen : IsOpenImmersion j.left]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) U)

include hregular hprojective hopen in
/-- The map from the regular projective completion to any proper
compactification is uniquely determined on the dense open curve. Existence
is the valuative extension at the boundary DVRs, uniqueness is separatedness.
This chooses geometry only, never a cohomology isomorphism. -/
theorem extension_existsUnique :
    ∃! f : C ⟶ P.obj.right, j ≫ f = P.obj.hom :=
  extension_existsUnique_of_regular U C j P

def extension {k : Type u} [Field k]
    (U C : SchemeOverField k) [Curve U] [Curve C]
    [hregular : Scheme.Regular C.left] [hprojective : Projective C.hom]
    (j : U ⟶ C) [hopen : IsOpenImmersion j.left]
    (P : Compactification.Of (Spec (CommRingCat.of k)) U) : C ⟶ P.obj.right :=
  (extension_existsUnique_of_regular U C j P).exists.choose

theorem extension_spec : j ≫ extension U C j P = P.obj.hom :=
  (extension_existsUnique_of_regular U C j P).exists.choose_spec

/-- The extension is proper since the source is proper and the target separated over k. -/
instance extension_proper : IsProper (extension U C j P).left := sorry

/-- A proper map from the dense regular completion is an isomorphism over
the common open interior. The cartesian condition excludes boundary points
mapping spuriously into the interior. -/
theorem interior_cartesian :
    IsPullback (𝟙 U.left) j.left (Compactification.Of.ι P) (extension U C j P).left := sorry

variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction j.left).op.HasLeftKanExtension F]
variable [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (smallEtalePullback (extension U C j P).left).op.HasLeftKanExtension F]

/-- The arbitrary-compactification cohomology endpoint maps to the regular
curve model by the explicit Ext pullback and extension-by-zero mate. -/
def cohomologyMap (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :=
  ActualCompactificationChange.cohomologyMap (Compactification.Of.ι P) j.left
    (extension U C j P).left (interior_cartesian U C j P) F i

def cohomologyEquiv (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ V : U.left.Etaleᵒᵖ, ∀ s : F.obj.obj V, IsOfFinAddOrder s) (i : ℕ) :=
  ActualCompactificationChange.cohomologyEquiv (Compactification.Of.ι P) j.left
    (extension U C j P).left (interior_cartesian U C j P) F hF i

end ActualCurveRefinement
