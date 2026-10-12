/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.Skyscraper
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.Algebra.Module.Graded.DegreeZero
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.BasicOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic

/-!
# Sheaves associated to graded modules on projective spectra

This module constructs the module sheaf on a projective spectrum whose local sections are
locally represented by degree-zero homogeneous fractions.  Its standard-open sections, stalks,
and degree-zero global sections are related to the corresponding homogeneous localizations by
explicit canonical linear maps.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.Proj.AssociatedModule

variable {R : Type u} {A M : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ)
variable (ℳ : ℤ → Submodule R M)
variable [SetLike.GradedSMul 𝒜 ℳ]

/-- The nonnegative pieces of an integer-graded module. -/
abbrev nonnegativeGrading : ℕ → Submodule R M := fun n ↦ ℳ (n : ℤ)

omit [Algebra R A] [AddSubgroupClass σ A] in
/-- Restricting an integer module grading to nonnegative degrees preserves its graded scalar
action. -/
@[instance]
theorem instGradedSMulNonnegativeGrading :
    SetLike.GradedSMul 𝒜 (nonnegativeGrading ℳ) where
  smul_mem := fun {i j a m} ha hm ↦ by
    simpa [nonnegativeGrading, AddAction.nat_vadd_int] using
      (SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha hm)

variable [GradedRing 𝒜]

/-- The degree-zero homogeneous localization of a graded module at a denominator submonoid. -/
noncomputable abbrev localization (P : Submonoid A) :=
  HomogeneousLocalization.Module.degreeZeroPart 𝒜 (nonnegativeGrading ℳ) P

/-- The degree-zero homogeneous localization away from a homogeneous element. -/
noncomputable abbrev away {d : ℕ} (f : 𝒜 d) :=
  localization 𝒜 ℳ (Submonoid.powers (f : A))

/-- The degree-zero homogeneous localization at the prime represented by a projective point. -/
noncomputable abbrev atPoint (x : AlgebraicGeometry.Proj 𝒜) :=
  localization 𝒜 ℳ x.asHomogeneousIdeal.toIdeal.primeCompl

/-- Enlarging denominators from a standard open to a point gives the canonical map on
degree-zero homogeneous localizations. -/
noncomputable def awayToPoint {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :
    away 𝒜 ℳ f → atPoint 𝒜 ℳ x.1 :=
  fun z ↦
    ⟨LocalizedModule.liftOfLE (Submonoid.powers (f : A))
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2) z,
      HomogeneousLocalization.Module.liftOfLE_mem_degreeZeroPart
        𝒜 (nonnegativeGrading ℳ) _ _ (Submonoid.powers_le.mpr x.2) z.2⟩

/-- The homogeneous localization at a projective point is canonically a module over the
structure-sheaf stalk at that point. -/
noncomputable instance atPointStalkModule (x : AlgebraicGeometry.Proj 𝒜) :
    Module ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPoint 𝒜 ℳ x) :=
  Module.compHom (atPoint 𝒜 ℳ x) (AlgebraicGeometry.Proj.stalkIso 𝒜 x).hom.hom

/-- Over an open neighborhood, the localization at a point is a module over the ring of
sections through the germ homomorphism. -/
noncomputable instance atPointSectionModule
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (x : U) :
    Module ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (atPoint 𝒜 ℳ x.1) :=
  Module.compHom (atPoint 𝒜 ℳ x.1)
    ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x.1 x.2).hom

/-- A point-family over an open assigns to each point its degree-zero homogeneous
localization. -/
abbrev PointFamily (U : (AlgebraicGeometry.Proj 𝒜).Opens) :=
  ∀ x : U, atPoint 𝒜 ℳ x.1

/-- A point-family is locally representable when it is locally induced by one homogeneous
fraction on a positive-degree standard open. -/
def IsLocallyRepresentable (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : PointFamily 𝒜 ℳ U) : Prop :=
  ∀ x : U,
    ∃ (d : ℕ) (f : 𝒜 d) (_ : 0 < d)
      (hU : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) ≤ U)
      (z : away 𝒜 ℳ f),
      x.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) ∧
        ∀ y : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A),
          s ⟨y.1, hU y.2⟩ = awayToPoint 𝒜 ℳ f y z

/-- The zero point-family is locally representable. -/
theorem zero_isLocallyRepresentable (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    IsLocallyRepresentable 𝒜 ℳ U 0 := sorry

/-- The sum of two locally representable point-families is locally representable. -/
theorem IsLocallyRepresentable.add {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    {s t : PointFamily 𝒜 ℳ U} (hs : IsLocallyRepresentable 𝒜 ℳ U s)
    (ht : IsLocallyRepresentable 𝒜 ℳ U t) :
    IsLocallyRepresentable 𝒜 ℳ U (s + t) := sorry

/-- Multiplying a locally representable point-family by a structure-sheaf section preserves
local representability. -/
theorem IsLocallyRepresentable.smul {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    {s : PointFamily 𝒜 ℳ U} (hs : IsLocallyRepresentable 𝒜 ℳ U s) :
    IsLocallyRepresentable 𝒜 ℳ U (r • s) := sorry

/-- Locally representable point-families form the module of associated sections on an open. -/
noncomputable def sections (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    Submodule ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (PointFamily 𝒜 ℳ U) where
  carrier := IsLocallyRepresentable 𝒜 ℳ U
  zero_mem' := zero_isLocallyRepresentable 𝒜 ℳ U
  add_mem' := IsLocallyRepresentable.add 𝒜 ℳ
  smul_mem' := IsLocallyRepresentable.smul 𝒜 ℳ

/-- Restriction of a locally representable family remains locally representable. -/
theorem restrict_isLocallyRepresentable
    {U V : (AlgebraicGeometry.Proj 𝒜).Opens} (hVU : V ≤ U)
    (s : sections 𝒜 ℳ U) :
    IsLocallyRepresentable 𝒜 ℳ V (fun x ↦ s.1 ⟨x.1, hVU x.2⟩) := by
  intro x
  obtain ⟨d, f, hd, hfU, z, hxf, hz⟩ := s.2 ⟨x.1, hVU x.2⟩
  obtain ⟨W, ⟨a, rfl⟩, hxa, haV⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)) x.2
  rw [AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj] at hxa
  obtain ⟨e, hxe⟩ := TopologicalSpace.Opens.mem_iSup.mp hxa
  let q : 𝒜 e := (DirectSum.decompose 𝒜 a) e
  have hxq : x.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (q : A) := by
    simpa only [q, GradedRing.proj_apply] using hxe
  have hqa : AlgebraicGeometry.Proj.basicOpen 𝒜 (q : A) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒜 a := by
    calc
      AlgebraicGeometry.Proj.basicOpen 𝒜 (q : A) ≤
          ⨆ i, AlgebraicGeometry.Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i a) := by
        simpa only [q, GradedRing.proj_apply] using
          (le_iSup (fun i ↦ AlgebraicGeometry.Proj.basicOpen 𝒜
            (GradedRing.proj 𝒜 i a)) e)
      _ = AlgebraicGeometry.Proj.basicOpen 𝒜 a :=
        (AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj 𝒜 a).symm
  let g : 𝒜 (d + e) :=
    ⟨(f : A) * (q : A), SetLike.GradedMul.mul_mem f.2 q.2⟩
  have hgpos : 0 < d + e := by omega
  have hg_open : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) =
      AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) ⊓
        AlgebraicGeometry.Proj.basicOpen 𝒜 (q : A) := by
    simpa only [g] using
      (AlgebraicGeometry.Proj.basicOpen_mul 𝒜 (f : A) (q : A))
  have hgf : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := by
    rw [hg_open]
    exact inf_le_left
  have hgV : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) ≤ V := by
    rw [hg_open]
    exact inf_le_right.trans (hqa.trans haV)
  have hxg : x.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) := by
    rw [hg_open]
    exact ⟨hxf, hxq⟩
  let z' : away 𝒜 ℳ g :=
    homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜
      (nonnegativeGrading ℳ) f.2 hd g.2 hgpos hgf z
  refine ⟨d + e, g, hgpos, hgV, z', hxg, ?_⟩
  intro y
  have hyf : y.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) := hgf y.2
  calc
    s.1 ⟨y.1, hVU (hgV y.2)⟩ =
        awayToPoint 𝒜 ℳ f ⟨y.1, hyf⟩ z := by
      simpa only using hz ⟨y.1, hyf⟩
    _ = awayToPoint 𝒜 ℳ g y z' := by
      apply Subtype.ext
      let P := y.1.asHomogeneousIdeal.toIdeal.primeCompl
      let sf : P := ⟨(f : A), hyf⟩
      let sg : P := ⟨(g : A), y.2⟩
      have hfg : (sf : A) ∣ (sg : A) := by
        exact ⟨(q : A), by rfl⟩
      have hz'_val : z'.1 =
          LocalizedModule.Away.mapOfDvd (M := M) (f : A) (g : A) hfg z.1 := by
        dsimp only [z']
        rw [homogeneousLocalizationAwayToAwayDegreeZeroModuleMap_val]
        simp only [localizationAwayToAwayModuleMap, LocalizedModule.Away.mapOfDvd]
        with_reducible_and_instances rfl
      have hnat := congrArg (fun F ↦ F z.1)
        (LocalizedModule.Away.toLocalizedModule_naturality
          (M := M) P sf sg hfg)
      change LocalizedModule.Away.toLocalizedModule P sf z.1 =
        LocalizedModule.Away.toLocalizedModule P sg z'.1
      rw [hz'_val]
      exact hnat.symm

/-- Restriction of associated sections along an inclusion of opens. -/
noncomputable def restrict {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (s : sections 𝒜 ℳ U) : sections 𝒜 ℳ V :=
  ⟨fun x ↦ s.1 ⟨x.1, hVU x.2⟩, restrict_isLocallyRepresentable 𝒜 ℳ hVU s⟩

/-- Restriction preserves addition of associated sections. -/
theorem restrict_add {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (s t : sections 𝒜 ℳ U) :
    restrict 𝒜 ℳ hVU (s + t) = restrict 𝒜 ℳ hVU s + restrict 𝒜 ℳ hVU t := by
  ext x
  rfl

/-- Restriction is semilinear over restriction of structure-sheaf sections. -/
theorem restrict_smul {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hVU : V ≤ U) (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (s : sections 𝒜 ℳ U) :
    restrict 𝒜 ℳ hVU (r • s) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hVU).op r •
        restrict 𝒜 ℳ hVU s := by
  ext x
  simp only [restrict, Submodule.coe_smul, Pi.smul_apply]
  have hres :=
    ((AlgebraicGeometry.Proj 𝒜).presheaf.germ_res_apply
      (homOfLE hVU) x.1 x.2 r).symm
  with_reducible_and_instances
    exact congrArg Subtype.val <| congrArg
      (fun q : (AlgebraicGeometry.Proj 𝒜).presheaf.stalk x.1 ↦
        q • s.1 ⟨x.1, hVU x.2⟩) hres

/-- Associated sections on an open, bundled as a module over structure-sheaf sections. -/
noncomputable abbrev sectionModule (U : (AlgebraicGeometry.Proj 𝒜).Opens) :=
  ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) (sections 𝒜 ℳ U)

/-- The restriction map between the modules of associated sections. -/
noncomputable def associatedRestrictionMap
    {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) :
    sectionModule 𝒜 ℳ U.unop ⟶
      (ModuleCat.restrictScalars ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom).obj
        (sectionModule 𝒜 ℳ V.unop) :=
  ModuleCat.ofHom
    (X := sectionModule 𝒜 ℳ U.unop)
    (Y := (ModuleCat.restrictScalars
      ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom).obj (sectionModule 𝒜 ℳ V.unop))
    { toFun := restrict 𝒜 ℳ i.unop.le
      map_add' := restrict_add 𝒜 ℳ i.unop.le
      map_smul' := restrict_smul 𝒜 ℳ i.unop.le }

/-- The restriction map associated to an identity inclusion is the canonical identity map. -/
theorem associatedRestrictionMap_id
    (U : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ) :
    associatedRestrictionMap 𝒜 ℳ (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((AlgebraicGeometry.Proj 𝒜).presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom
          ((AlgebraicGeometry.Proj 𝒜).presheaf.map_id U))).inv.app _ := by
  ext s
  rfl

/-- Associated restriction maps compose functorially. -/
theorem associatedRestrictionMap_comp
    {U V W : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    associatedRestrictionMap 𝒜 ℳ (i ≫ j) =
      associatedRestrictionMap 𝒜 ℳ i ≫
        (ModuleCat.restrictScalars _).map (associatedRestrictionMap 𝒜 ℳ j) ≫
          (ModuleCat.restrictScalarsComp'
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map i).hom
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map j).hom
            ((AlgebraicGeometry.Proj 𝒜).presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom
              ((AlgebraicGeometry.Proj 𝒜).presheaf.map_comp i j))).inv.app _ := by
  ext s
  rfl

/-- The presheaf of locally representable degree-zero homogeneous fractions. -/
noncomputable def presheaf :
    PresheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj where
  obj U := sectionModule 𝒜 ℳ U.unop
  map i := associatedRestrictionMap 𝒜 ℳ i
  map_id := associatedRestrictionMap_id 𝒜 ℳ
  map_comp := associatedRestrictionMap_comp 𝒜 ℳ

/-- Locally representable homogeneous-fraction sections satisfy the sheaf condition. -/
theorem associatedPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜))
      (presheaf 𝒜 ℳ).presheaf := sorry

/-- The deterministic sheaf associated to an integer-graded module on a projective spectrum. -/
noncomputable def sheaf : (AlgebraicGeometry.Proj 𝒜).Modules where
  val := presheaf 𝒜 ℳ
  isSheaf := associatedPresheaf_isSheaf 𝒜 ℳ

/-- A degree-zero fraction defines a locally representable section on its positive-degree
standard open. -/
theorem awaySection_isLocallyRepresentable {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : away 𝒜 ℳ f) :
    IsLocallyRepresentable 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))
      (fun x ↦ awayToPoint 𝒜 ℳ f x z) := by
  intro x
  exact ⟨d, f, hd, le_rfl, z, x.2, fun _ ↦ rfl⟩

/-- The section on a standard open represented by a degree-zero homogeneous fraction. -/
noncomputable def awaySection {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : away 𝒜 ℳ f) :
    sections 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :=
  ⟨fun x ↦ awayToPoint 𝒜 ℳ f x z,
    awaySection_isLocallyRepresentable 𝒜 ℳ f hd z⟩

/-- The standard-open fraction section associated to zero is zero. -/
theorem awaySection_zero {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    awaySection 𝒜 ℳ f hd 0 = 0 := sorry

/-- The standard-open fraction-section construction preserves addition. -/
theorem awaySection_add {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (x y : away 𝒜 ℳ f) :
    awaySection 𝒜 ℳ f hd (x + y) =
      awaySection 𝒜 ℳ f hd x + awaySection 𝒜 ℳ f hd y := by
  ext z
  change
    LocalizedModule.liftOfLE (Submonoid.powers (f : A))
        z.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr z.2) (x + y).1 =
      LocalizedModule.liftOfLE (Submonoid.powers (f : A))
          z.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr z.2) x.1 +
        LocalizedModule.liftOfLE (Submonoid.powers (f : A))
          z.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr z.2) y.1
  exact (LocalizedModule.liftOfLE (Submonoid.powers (f : A))
    z.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr z.2)).map_add x.1 y.1

/-- The standard-open fraction-section construction is linear over the canonical chart
identification. -/
theorem awaySection_smul {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 (f : A)) (x : away 𝒜 ℳ f) :
    awaySection 𝒜 ℳ f hd (r • x) =
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom r •
        awaySection 𝒜 ℳ f hd x := sorry

/-- The canonical linear map from degree-zero homogeneous fractions to sections on a positive
standard open. -/
noncomputable def awaySectionLinearMap {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    away 𝒜 ℳ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          (sectionModule 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))) where
  toFun := awaySection 𝒜 ℳ f hd
  map_add' := awaySection_add 𝒜 ℳ f hd
  map_smul' := awaySection_smul 𝒜 ℳ f hd

/-- On every positive-degree standard open, the canonical fraction-to-section linear map is
bijective. -/
theorem awaySectionLinearMap_bijective {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    Function.Bijective (awaySectionLinearMap 𝒜 ℳ f hd) := sorry

/-- Restriction of a standard-open fraction section agrees with the canonical map between the
corresponding degree-zero homogeneous localizations. -/
theorem awaySectionLinearMap_restriction
    {d e : ℕ} (f : 𝒜 d) (hd : 0 < d) (g : 𝒜 e) (he : 0 < e)
    (hgf : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) ≤
      AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) (z : away 𝒜 ℳ f) :
    restrict 𝒜 ℳ hgf (awaySection 𝒜 ℳ f hd z) =
      awaySection 𝒜 ℳ g he
        (homogeneousLocalizationAwayToAwayDegreeZeroModuleMap 𝒜
          (nonnegativeGrading ℳ) f.2 hd g.2 he hgf z) := sorry

/-- The canonical ring map from the degree-zero ring to global functions on the projective
spectrum. -/
noncomputable def degreeZeroRingHom :
    𝒜 0 →+* (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
    (AlgebraicGeometry.Proj.toSpecZero 𝒜).appTop).hom

/-- A degree-zero module element defines an element of every point localization by the fraction
with denominator one. -/
noncomputable def degreeZeroAtPoint (m : ℳ 0) (x : AlgebraicGeometry.Proj 𝒜) :
    atPoint 𝒜 ℳ x :=
  ⟨LocalizedModule.mk (m : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl),
    HomogeneousLocalization.Module.mk_mem_degreeZeroPart 𝒜
      (nonnegativeGrading ℳ) x.asHomogeneousIdeal.toIdeal.primeCompl m
      (1 : 𝒜 0) (by simp)⟩

/-- The point-family induced by a degree-zero element is locally representable. -/
theorem degreeZeroSection_isLocallyRepresentable (m : ℳ 0) :
    IsLocallyRepresentable 𝒜 ℳ ⊤ (fun x ↦ degreeZeroAtPoint 𝒜 ℳ m x.1) := sorry

/-- The global associated-sheaf section induced by a degree-zero module element. -/
noncomputable def degreeZeroSection (m : ℳ 0) : sections 𝒜 ℳ ⊤ :=
  ⟨fun x ↦ degreeZeroAtPoint 𝒜 ℳ m x.1,
    degreeZeroSection_isLocallyRepresentable 𝒜 ℳ m⟩

/-- The global section induced by the zero degree-zero element is zero. -/
theorem degreeZeroSection_zero :
    degreeZeroSection 𝒜 ℳ 0 = 0 := sorry

/-- The global-section construction on degree zero preserves addition. -/
theorem degreeZeroSection_add (x y : ℳ 0) :
    degreeZeroSection 𝒜 ℳ (x + y) =
      degreeZeroSection 𝒜 ℳ x + degreeZeroSection 𝒜 ℳ y := by
  ext z
  change LocalizedModule.mk ((x + y : ℳ 0) : M) 1 =
    LocalizedModule.mk (x : M) 1 + LocalizedModule.mk (y : M) 1
  simpa only [Submodule.coe_add, Submodule.coe_mk, one_smul, one_mul] using
    (LocalizedModule.mk_add_mk (m1 := (x : M)) (m2 := (y : M))
      (s1 := (1 : z.1.asHomogeneousIdeal.toIdeal.primeCompl))
      (s2 := (1 : z.1.asHomogeneousIdeal.toIdeal.primeCompl))).symm

/-- The global-section construction on degree zero is linear over the canonical degree-zero ring
map. -/
theorem degreeZeroSection_smul (r : 𝒜 0) (x : ℳ 0) :
    degreeZeroSection 𝒜 ℳ (r • x) =
      degreeZeroRingHom 𝒜 r • degreeZeroSection 𝒜 ℳ x := sorry

/-- The canonical degree-zero linear map to global sections of the associated sheaf. -/
noncomputable def degreeZeroToGlobalSections :
    ℳ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj (sectionModule 𝒜 ℳ ⊤) where
  toFun := degreeZeroSection 𝒜 ℳ
  map_add' := degreeZeroSection_add 𝒜 ℳ
  map_smul' := degreeZeroSection_smul 𝒜 ℳ

/-- On a positive-degree standard open, the degree-zero global-section map is the fraction map
with denominator one. -/
theorem degreeZeroToGlobalSections_away {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (m : ℳ 0) :
    restrict 𝒜 ℳ le_top
        (degreeZeroToGlobalSections 𝒜 ℳ m) =
      awaySection 𝒜 ℳ f hd
        ⟨LocalizedModule.mk (m : M) (1 : Submonoid.powers (f : A)),
          HomogeneousLocalization.Module.mk_mem_degreeZeroPart 𝒜
            (nonnegativeGrading ℳ) (Submonoid.powers (f : A)) m
            (1 : 𝒜 0) (by simp)⟩ := sorry

/-- Evaluation of an associated section at a point of its domain. -/
noncomputable def sectionEvaluation
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (x : AlgebraicGeometry.Proj 𝒜)
    (hx : x ∈ U) :
    sectionModule 𝒜 ℳ U ⟶
      (ModuleCat.restrictScalars
        ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x hx).hom).obj
          (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
            (atPoint 𝒜 ℳ x)) :=
  ModuleCat.ofHom
    (X := sectionModule 𝒜 ℳ U)
    (Y := (ModuleCat.restrictScalars
      ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x hx).hom).obj
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPoint 𝒜 ℳ x)))
    { toFun := fun s ↦ s.1 ⟨x, hx⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The component on an open of the evaluation morphism from associated sections to the
skyscraper of a point localization. -/
noncomputable def pointSkyscraperApp (x : AlgebraicGeometry.Proj 𝒜)
    (U : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ) :
    (presheaf 𝒜 ℳ).obj U ⟶
      PresheafOfModules.Skyscraper.obj (AlgebraicGeometry.Proj 𝒜).presheaf x
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPoint 𝒜 ℳ x)) U :=
  @dite _ (x ∈ U.unop) (Classical.dec _)
    (fun hx ↦ sectionEvaluation 𝒜 ℳ U.unop x hx ≫
      eqToHom
        (dif_pos hx :
          PresheafOfModules.Skyscraper.obj (AlgebraicGeometry.Proj 𝒜).presheaf x
              (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
                (atPoint 𝒜 ℳ x)) U =
            (ModuleCat.restrictScalars
              ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U.unop x hx).hom).obj
                (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
                  (atPoint 𝒜 ℳ x))).symm)
    (fun _ ↦ 0)

/-- Point evaluation commutes with restriction of associated sections. -/
theorem pointSkyscraperApp_naturality (x : AlgebraicGeometry.Proj 𝒜)
    {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) :
    (presheaf 𝒜 ℳ).map i ≫
        (ModuleCat.restrictScalars
          ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.map i).hom).map
            (pointSkyscraperApp 𝒜 ℳ x V) =
      pointSkyscraperApp 𝒜 ℳ x U ≫
        PresheafOfModules.Skyscraper.map (AlgebraicGeometry.Proj 𝒜).presheaf x
          (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
            (atPoint 𝒜 ℳ x)) i := by
  classical
  by_cases hV : x ∈ V.unop
  · have hU : x ∈ U.unop := i.unop.le hV
    let O := (AlgebraicGeometry.Proj 𝒜).presheaf
    let N := ModuleCat.of (O.stalk x) (atPoint 𝒜 ℳ x)
    let hObjU : PresheafOfModules.Skyscraper.obj O x N U =
        (ModuleCat.restrictScalars (O.germ U.unop x hU).hom).obj N :=
      PresheafOfModules.Skyscraper.obj_eq_of_mem O x N U hU
    let hObjV : PresheafOfModules.Skyscraper.obj O x N V =
        (ModuleCat.restrictScalars (O.germ V.unop x hV).hom).obj N :=
      PresheafOfModules.Skyscraper.obj_eq_of_mem O x N V hV
    let hGerm : (O.germ U.unop x hU).hom =
        (O.germ V.unop x hV).hom.comp (O.map i).hom :=
      PresheafOfModules.Skyscraper.germ_comp O x i hV
    simp only [pointSkyscraperApp, PresheafOfModules.Skyscraper.map,
      dif_pos hV, dif_pos hU]
    change
      (presheaf 𝒜 ℳ).map i ≫
          (ModuleCat.restrictScalars (O.map i).hom).map
            (sectionEvaluation 𝒜 ℳ V.unop x hV ≫ eqToHom hObjV.symm) =
        (sectionEvaluation 𝒜 ℳ U.unop x hU ≫ eqToHom hObjU.symm) ≫
          eqToHom hObjU ≫
            (ModuleCat.restrictScalarsComp'App (O.map i).hom
              (O.germ V.unop x hV).hom (O.germ U.unop x hU).hom hGerm N).hom ≫
              (ModuleCat.restrictScalars (O.map i).hom).map (eqToHom hObjV.symm)
    simp only [Functor.map_comp, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    ext s
    rfl
  · by_cases hU : x ∈ U.unop
    · simp only [pointSkyscraperApp, PresheafOfModules.Skyscraper.map,
        dif_neg hV, dif_pos hU, Functor.comp_map]
      ext s
      rfl
    · simp only [pointSkyscraperApp, PresheafOfModules.Skyscraper.map,
        dif_neg hV, dif_neg hU, Functor.comp_map]
      rfl

/-- The associated presheaf maps canonically to the skyscraper of its localization at a point. -/
noncomputable def pointSkyscraperHom (x : AlgebraicGeometry.Proj 𝒜) :
    presheaf 𝒜 ℳ ⟶
      PresheafOfModules.Skyscraper.atPoint (AlgebraicGeometry.Proj 𝒜).presheaf x
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPoint 𝒜 ℳ x)) where
  app := pointSkyscraperApp 𝒜 ℳ x
  naturality := pointSkyscraperApp_naturality 𝒜 ℳ x

/-- The canonical linear map from the stalk of the associated sheaf to the homogeneous
localization at the corresponding projective point. -/
noncomputable def stalkToPointLinearMap (x : AlgebraicGeometry.Proj 𝒜) :
    RingedSpace.stalkModuleCat (sheaf 𝒜 ℳ) x ⟶
      ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x) (atPoint 𝒜 ℳ x) :=
  PresheafOfModules.Skyscraper.fromHom (AlgebraicGeometry.Proj 𝒜).presheaf x
    (pointSkyscraperHom 𝒜 ℳ x)

/-- The canonical stalk map sends the germ of a section to its value in the point
localization. -/
theorem stalkToPointLinearMap_germ (x : AlgebraicGeometry.Proj 𝒜)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (hx : x ∈ U)
    (s : sections 𝒜 ℳ U) :
    stalkToPointLinearMap 𝒜 ℳ x
        (TopCat.Presheaf.germ (sheaf 𝒜 ℳ).val.presheaf U x hx s) =
      s.1 ⟨x, hx⟩ := sorry

/-- The canonical map from an associated-sheaf stalk to its point localization is bijective. -/
theorem stalkToPointLinearMap_bijective (x : AlgebraicGeometry.Proj 𝒜) :
    Function.Bijective (stalkToPointLinearMap 𝒜 ℳ x) := sorry

/-- The sheaf associated to a graded module is zero when a power of the irrelevant ideal
annihilates the module. -/
theorem sheaf_isZero_of_irrelevant_pow_le_annihilator (n : ℕ)
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ n ≤ Module.annihilator A M) :
    CategoryTheory.Limits.IsZero (sheaf 𝒜 ℳ) := sorry

/-- After passage to a stalk, the degree-zero global-section map sends a homogeneous element to
the fraction with denominator one. -/
theorem degreeZeroToGlobalSections_stalk (x : AlgebraicGeometry.Proj 𝒜) (m : ℳ 0) :
    stalkToPointLinearMap 𝒜 ℳ x
        (TopCat.Presheaf.germ (sheaf 𝒜 ℳ).val.presheaf ⊤ x trivial
          (degreeZeroToGlobalSections 𝒜 ℳ m)) =
      degreeZeroAtPoint 𝒜 ℳ m x := sorry

end AlgebraicGeometry.Proj.AssociatedModule
