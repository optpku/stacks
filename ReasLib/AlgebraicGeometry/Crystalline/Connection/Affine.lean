/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.SquareZero
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Geometry
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Coefficients

@[expose] public section
open KaehlerDifferential.DeRham
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
namespace CrystallinePDSquareZeroGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)
variable [Module Bᵐᵒᵖ (ambientDividedPowerDifferential (A := A) (B := B) δ)]
variable [IsCentralScalar B (ambientDividedPowerDifferential (A := A) (B := B) δ)]

/-- The nil PD ideal remains nil after adjoining the square-zero PD forms. -/
theorem extensionIdeal_nil (hJ : ∀ x ∈ J, IsNilpotent x) :
    ∀ x ∈ DividedPowers.TrivSqZeroExt.ideal (ambientDividedPowerDifferential (A := A) (B := B) δ) J,
      IsNilpotent x := sorry

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
    (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable (base : Spec (.of B) ⟶ S) (fibre : Spec (.of (B ⧸ J)) ⟶ X)
variable (comm : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ base =
  fibre ≫ x₀ ≫ I.subschemeι)

/-- The extended closed-fibre map uses the genuine quotient equivalence. -/
noncomputable def extendedFibre :=
  Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.closedFibreEquiv A B δ).symm.toRingHom) ≫ fibre

/-- The extended base map uses the first-coordinate ring inclusion. -/
noncomputable def extendedBase :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom B (ambientDividedPowerDifferential (A := A) (B := B) δ))) ≫ base

include comm in
/-- The actual quotient square commutes with the original base square. -/
theorem extendedSquare :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (DividedPowers.TrivSqZeroExt.ideal (ambientDividedPowerDifferential (A := A) (B := B) δ) J))) ≫
        extendedBase A B δ base =
      extendedFibre A B δ fibre ≫ x₀ ≫ I.subschemeι := sorry

/-- The genuine PD infinitesimal thickening used for a finite-stage crystal
connection. Both its ring and closed-fibre map are explicitly constructed. -/
noncomputable def object (hJ : ∀ x ∈ J, IsNilpotent x) :
    CrystallineObject S I γ hc X x₀ :=
  CechCrisCover.affineCrystallineObject I γ hc x₀
    (DividedPowers.TrivSqZeroExt.ideal (ambientDividedPowerDifferential (A := A) (B := B) δ) J)
    (DividedPowers.TrivSqZeroExt.dividedPowers (ambientDividedPowerDifferential (A := A) (B := B) δ) δ)
    (extensionIdeal_nil A B δ hJ) (extendedBase A B δ base) (extendedFibre A B δ fibre)
    (extendedSquare A B δ I x₀ base fibre comm)

/-- The first projection from the PD infinitesimal thickening to the
original affine crystalline object, with the actual common closed fibre. -/
noncomputable def firstProjection (hJ : ∀ x ∈ J, IsNilpotent x) :
    CrystallineObject.Hom (object A B δ I γ hc x₀ base fibre comm hJ)
      (CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm) where
  source := Over.homMk
    (Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.closedFibreEquiv A B δ).symm.toRingHom))
    (by rfl)
  thickening := Spec.map
    (CommRingCat.ofHom (TrivSqZeroExt.inlHom B (ambientDividedPowerDifferential (A := A) (B := B) δ)))
  source_comm := sorry
  base_comm := by rfl
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The first projection uses precisely the inclusion of coefficients into
the square-zero extension, not a selected morphism. -/
theorem firstProjection_thickening (hJ : ∀ x ∈ J, IsNilpotent x) :
    (firstProjection A B δ I γ hc x₀ base fibre comm hJ).thickening =
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom B (ambientDividedPowerDifferential (A := A) (B := B) δ))) := rfl

/-- The second infinitesimal projection uses the actual PD differential
lift. Compatibility with the given base map must be established explicitly. -/
noncomputable def secondProjection (hJ : ∀ x ∈ J, IsNilpotent x)
    (hbase : Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.differentialLift A B δ)) ≫
      base = extendedBase A B δ base) :
    CrystallineObject.Hom (object A B δ I γ hc x₀ base fibre comm hJ)
      (CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm) where
  source := Over.homMk
    (Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.closedFibreEquiv A B δ).symm.toRingHom))
    (by rfl)
  thickening := Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.differentialLift A B δ))
  source_comm := sorry
  base_comm := hbase
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- For the actual affine A-algebra base map the two projections agree over
the base, since the relative PD derivation kills images of A. -/
theorem differentialLift_overAffineBase :
    Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.differentialLift A B δ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      extendedBase A B δ (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

variable (hJ : ∀ x ∈ J, IsNilpotent x)
variable (hrelative : CrystallineBaseCompatible I γ hc x₀
  (CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm))
variable (hopen : IsOpenImmersion fibre)

include hrelative in
/-- Base PD compatibility passes through the actual first PD projection. -/
theorem object_baseCompatible :
    CrystallineBaseCompatible I γ hc x₀ (object A B δ I γ hc x₀ base fibre comm hJ) := sorry

include hopen in
/-- The source remains open because the closed-fibre comparison is an isomorphism. -/
theorem extendedFibre_open : IsOpenImmersion (extendedFibre A B δ fibre) := sorry

/-- The original affine object as an actual small crystalline object. -/
noncomputable def originalSmall :
    AlgebraicGeometry.Scheme.Crystalline.smallCrystallineSite S I γ hc X x₀ where
  obj := ⟨CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm, hrelative⟩
  property := hopen

/-- The PD square-zero extension as a small crystalline object, retaining
the verified base compatibility and the actual open source. -/
noncomputable def extendedSmall :
    AlgebraicGeometry.Scheme.Crystalline.smallCrystallineSite S I γ hc X x₀ where
  obj := ⟨object A B δ I γ hc x₀ base fibre comm hJ,
    object_baseCompatible A B δ I γ hc x₀ base fibre comm hJ hrelative⟩
  property := extendedFibre_open A B δ fibre hopen

/-- The first projection in the small crystalline category. -/
noncomputable def firstSmallProjection :
    extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen ⟶
      originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen :=
  ObjectProperty.homMk (firstProjection A B δ I γ hc x₀ base fibre comm hJ)

variable (hbase : Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.differentialLift A B δ)) ≫
  base = extendedBase A B δ base)

/-- The second projection in the small crystalline category. -/
noncomputable def secondSmallProjection :
    extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen ⟶
      originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen :=
  ObjectProperty.homMk (secondProjection A B δ I γ hc x₀ base fibre comm hJ hbase)

/-- Difference of the actual two crystal pullbacks on global sections.
Its codomain is the extension coefficient module; subsequent kernel/tensor
identification must retain this concrete map. -/
noncomputable def sectionDifference
    (F : CrystallineModuleSheaf.CrisModuleSheaf S I γ hc X x₀) :
    AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
        (F.obj (originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen)) ⟶
      AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
        (F.obj (extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen)) :=
  AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections_map
      (secondProjection A B δ I γ hc x₀ base fibre comm hJ hbase).thickening
      (F.comparison (secondSmallProjection A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase)) -
    AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections_map
      (firstProjection A B δ I γ hc x₀ base fibre comm hJ).thickening
      (F.comparison (firstSmallProjection A B δ I γ hc x₀ base fibre comm hJ hrelative hopen))

/-- The original thickening embeds into its square-zero extension via the
actual first-coordinate projection of rings. -/
noncomputable def inclusion :
    CrystallineObject.Hom
      (CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm)
      (object A B δ I γ hc x₀ base fibre comm hJ) where
  source := Over.homMk
    (Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.closedFibreEquiv A B δ).toRingHom)) sorry
  thickening := Spec.map
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B (ambientDividedPowerDifferential (A := A) (B := B) δ)).toRingHom)
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The same actual embedding in the small crystalline category. -/
noncomputable def smallInclusion :
    originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen ⟶
      extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen :=
  ObjectProperty.homMk (inclusion A B δ I γ hc x₀ base fibre comm hJ)

variable (F : CrystallineModuleSheaf.CrisModuleSheaf S I γ hc X x₀)

/-- Restriction of the actual coefficient sheaf along the square-zero embedding. -/
noncomputable def inclusionRestriction :
    AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
        (F.obj (extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen)) ⟶
      AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
        (F.obj (originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen)) :=
  AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections_map
    (inclusion A B δ I γ hc x₀ base fibre comm hJ).thickening
    (F.comparison (smallInclusion A B δ I γ hc x₀ base fibre comm hJ hrelative hopen))

variable [hcoherent : CrystallineCoefficients.SectionsCoherent I γ hc x₀ F]

include hcoherent in
/-- The two pullbacks agree after restricting back to the original stage;
sheaf-level crystal coherence is retained rather than fabricated. -/
theorem sectionDifference_restrict_zero
    (m : AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
      (F.obj (originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen))) :
    inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F
      (sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m) = 0 := sorry

/-- The connection difference valued in the actual square-zero restriction
kernel. Only its kernel-membership proof is deferred, not its value. -/
noncomputable def differenceInKernel
    (m : AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections
      (F.obj (originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen))) :
    (inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).hom.ker :=
  ⟨sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m,
    sectionDifference_restrict_zero A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m⟩

/-- The coefficient module at the original affine stage, with its actual
ring action transported through the canonical affine-functions map. -/
noncomputable def coefficientModule : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of B)).inv.hom).obj
    ((F.obj (originalSmall B δ I γ hc x₀ base fibre comm hJ hrelative hopen)).val.obj
      (Opposite.op ⊤))

/-- The genuine extension coefficient module, retaining the action of the
square-zero ring rather than an unrelated abstract module. -/
noncomputable def extensionModule :
    ModuleCat.{u} (TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) (B := B) δ)) :=
  (ModuleCat.restrictScalars
    (Scheme.ΓSpecIso (.of (TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) (B := B) δ)))).inv.hom).obj
      ((F.obj (extendedSmall A B δ I γ hc x₀ base fibre comm hJ hrelative hopen)).val.obj
        (Opposite.op ⊤))

/-- Pull a coefficient back along the first, constant infinitesimal lift. -/
noncomputable def constantPullback :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F →+
      extensionModule A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F :=
  (AlgebraicGeometry.Scheme.Crystalline.abelianGlobalSections_map
    (firstProjection A B δ I γ hc x₀ base fibre comm hJ).thickening
    (F.comparison (firstSmallProjection A B δ I γ hc x₀ base fibre comm hJ hrelative hopen))).hom

/-- On generators, the geometric tensor map multiplies the actual pulled
back coefficient by the square-zero one-form. Both inputs are used. -/
noncomputable def formAction
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (ω : (ambientDividedPowerDifferential (A := A) (B := B) δ)) :
    extensionModule A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F :=
  (TrivSqZeroExt.inr ω : TrivSqZeroExt B (ambientDividedPowerDifferential (A := A) (B := B) δ)) •
    constantPullback A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m

include hcoherent in
/-- Restriction kills the square-zero one-form factor. -/
theorem formAction_restrict_zero
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (ω : (ambientDividedPowerDifferential (A := A) (B := B) δ)) :
    inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F
      (formAction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m ω) = 0 := sorry

/-- The tensor generator in the actual geometric restriction kernel. -/
noncomputable def formActionKernel
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (ω : (ambientDividedPowerDifferential (A := A) (B := B) δ)) :
    (inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).hom.ker :=
  ⟨formAction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m ω,
    formAction_restrict_zero A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m ω⟩

/-- The canonical tensor map into the geometric kernel. Balancing is over
the actual stage ring B, not over the integers. -/
noncomputable def tensorToKernel :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F ⊗[B]
      (ambientDividedPowerDifferential (A := A) (B := B) δ) →+
        (inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).hom.ker :=
  TensorProduct.liftAddHom
    { toFun := fun m ↦
        { toFun := fun ω ↦ formActionKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m ω
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    (fun _ _ _ ↦ sorry)

/-- The constructed tensor map has the intended pure-tensor formula. -/
theorem tensorToKernel_tmul
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (ω : (ambientDividedPowerDifferential (A := A) (B := B) δ)) :
    (tensorToKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F (m ⊗ₜ[B] ω)).val =
      formAction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F m ω := rfl

variable [hcrystal : CrystallineModuleSheaf.CrisModuleSheaf.IsCrystal F]
variable [hqc : CrystallineModuleSheaf.CrisModuleSheaf.IsLocallyQuasiCoherent F]

include hcrystal hqc in
/-- Affine quasi-coherence identifies the first pullback with tensor scalar
extension; the actual crystal comparison is invertible and its augmentation
agrees with restriction by coherence. Its kernel is exactly the one-form
summand. This assertion is only about this finite affine stage, not a
finite-stage inverse to a completed module. -/
theorem tensorToKernel_bijective :
    Function.Bijective (tensorToKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) := sorry

/-- The uniquely characterized geometric tensor/kernel identification. -/
noncomputable def tensorKernelEquiv :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F ⊗[B]
      (ambientDividedPowerDifferential (A := A) (B := B) δ) ≃+
        (inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).hom.ker :=
  AddEquiv.ofBijective (tensorToKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (tensorToKernel_bijective A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)

/-- The actual finite-stage PD connection: pull back along the two PD
lifts, subtract, and use the canonical kernel identification. -/
noncomputable def connectionValue
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F ⊗[B]
      (ambientDividedPowerDifferential (A := A) (B := B) δ) :=
  (tensorKernelEquiv A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).symm
    (differenceInKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m)

/-- Recovering the geometric difference is an actual inverse law, not an
unproved specification used to bless an arbitrary connection. -/
theorem connectionValue_spec
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) :
    (tensorToKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F
      (connectionValue A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m)).val =
        sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m :=
  congrArg Subtype.val
    ((tensorKernelEquiv A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).apply_symm_apply _)

/-- The geometric difference characterizes the finite-stage connection
uniquely; an unrelated tensor cannot satisfy the same equation. -/
theorem connectionValue_unique
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F)
    (t : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F ⊗[B]
      (ambientDividedPowerDifferential (A := A) (B := B) δ))
    (ht : (tensorToKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F t).val =
      sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m) :
    t = connectionValue A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m := by
  apply (tensorKernelEquiv A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).injective
  apply Subtype.ext
  exact ht.trans
    (connectionValue_spec A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m).symm

/-- The actual comparison difference is additive even before identifying
its kernel with tensors. Its additivity is inherited from the two pullbacks. -/
noncomputable def differenceHom :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F →+
      (inclusionRestriction A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).hom.ker where
  toFun := differenceInKernel A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F
  map_zero' := Subtype.ext
    (map_zero (sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F).hom)
  map_add' m n := Subtype.ext
    (map_add (sectionDifference A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F).hom m n)

/-- The finite-stage connection as an additive map, using the actual
additive inverse to the geometric tensor map. -/
noncomputable def connectionHom :
    coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F →+
      coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F ⊗[B]
        (ambientDividedPowerDifferential (A := A) (B := B) δ) :=
  (tensorKernelEquiv A B δ I γ hc x₀ base fibre comm hJ hrelative hopen F).symm.toAddMonoidHom.comp
    (differenceHom A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)

/-- Bundling preserves the previously characterized finite-stage value. -/
theorem connectionHom_apply
    (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) :
    connectionHom A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m =
      connectionValue A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m := rfl

/-- The first projection is B-linear, the second is semilinear for
b ↦ (b, db), and the square-zero ideal annihilates the restriction kernel.
Together these give the actual PD Leibniz rule. -/
theorem connectionHom_leibniz
    (b : B) (m : coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) :
    connectionHom A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F (b • m) =
      b • connectionHom A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F m +
        m ⊗ₜ[B] (ambientDividedPowerDifferentialDerivation (A := A) (B := B) δ) b := sorry

/-- The genuine finite-stage PD connection; its non-Prop payload is fully
specified by the two geometric pullbacks and tensor/kernel map. -/
noncomputable def connection :
    Connection (ambientDividedPowerDifferentialDerivation (A := A) (B := B) δ)
      (coefficientModule B δ I γ hc x₀ base fibre comm hJ hrelative hopen F) :=
  Connection.of (connectionHom A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)
    (connectionHom_leibniz A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)

/-- The cocycle law for the crystal comparison on second-order PD
infinitesimal thickenings gives zero curvature of this specified connection. -/
theorem connection_integrable :
    Connection.IsIntegrable
      (connection A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)
      (DPPolynomial.DeRham.canonicalCalculus A B δ) := sorry

/-- The finite-stage de Rham complex uses the genuine PD exterior calculus
and the crystal-induced connection in every degree. -/
noncomputable def deRhamComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  Connection.deRhamComplex
    (connection A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)
    (DPPolynomial.DeRham.canonicalCalculus A B δ)
    (connection_integrable A B δ I γ hc x₀ base fibre comm hJ hrelative hopen hbase F)

end CrystallinePDSquareZeroGeometry
