/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactificationTransport
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommIdentityCompactification
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable (X : SchemeOverField k) [Projective X.hom]

/-- The identity compactification is actual geometric data, independent of cohomology. -/
def object : Compactification.Of (Spec (CommRingCat.of k)) X :=
  Compactification.Of.mk (Spec (CommRingCat.of k)) X (𝟙 X)

/-- The identity compactification morphism is étale. -/
instance identity_etale : Etale (Compactification.Of.ι (object X)) :=
  inferInstanceAs (Etale (𝟙 X.left))

/-- The étale-site equivalence induced by the identity compactification. -/
def siteIso : etaleRestriction (Compactification.Of.ι (object X)) ≅ 𝟭 X.left.Etale :=
  MorphismProperty.Over.mapId (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
    X.left (Compactification.Of.ι (object X)) rfl

/-- The induced equivalence on sheaves of R-modules. -/
def restrictionIso : etaleRestrictionSheaf (Compactification.Of.ι (object X))
    (ModuleCat.{u + 1} R) ≅ 𝟭 (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun U ↦ F.obj.map (((siteIso X).inv.app U.unop).op)
          naturality := by sorry }
      inv := ObjectProperty.homMk
        { app := fun U ↦ F.obj.map (((siteIso X).hom.app U.unop).op)
          naturality := by sorry }
      hom_inv_id := by sorry
      inv_hom_id := by sorry }) (by sorry)

/-- Naturality of the hom component of the sheaf restriction equivalence. -/
theorem restrictionIso_hom_naturality (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    ∀ ⦃sourceObj targetObj : X.left.Etaleᵒᵖ⦄ (siteMorphism : sourceObj ⟶ targetObj),
      ((etaleRestrictionSheaf (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F).obj.map
          siteMorphism ≫ ((restrictionIso R X).hom.app F).hom.app targetObj =
        ((restrictionIso R X).hom.app F).hom.app sourceObj ≫ F.obj.map siteMorphism :=
  ((restrictionIso R X).hom.app F).hom.naturality

/-- Naturality of the inverse component of the sheaf restriction equivalence. -/
theorem restrictionIso_inv_naturality (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    ∀ ⦃sourceObj targetObj : X.left.Etaleᵒᵖ⦄ (siteMorphism : sourceObj ⟶ targetObj),
      F.obj.map siteMorphism ≫ ((restrictionIso R X).inv.app F).hom.app targetObj =
        ((restrictionIso R X).inv.app F).hom.app sourceObj ≫
          ((etaleRestrictionSheaf (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F).obj.map
            siteMorphism :=
  ((restrictionIso R X).inv.app F).hom.naturality

/-- The hom followed by inverse is the identity on each restricted sheaf. -/
theorem restrictionIso_hom_inv_id (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (restrictionIso R X).hom.app F ≫ (restrictionIso R X).inv.app F = 𝟙 _ :=
  (restrictionIso R X).hom_inv_id_app F

/-- The inverse followed by hom is the identity on each sheaf. -/
theorem restrictionIso_inv_hom_id (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (restrictionIso R X).inv.app F ≫ (restrictionIso R X).hom.app F = 𝟙 _ :=
  (restrictionIso R X).inv_hom_id_app F

/-- Naturality of the sheaf restriction equivalence in its sheaf argument. -/
theorem restrictionIso_naturality :
    ∀ ⦃sourceSheaf targetSheaf : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)⦄
      (sheafMorphism : sourceSheaf ⟶ targetSheaf),
      (etaleRestrictionSheaf (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).map
          sheafMorphism ≫ (restrictionIso R X).hom.app targetSheaf =
        (restrictionIso R X).hom.app sourceSheaf ≫ sheafMorphism :=
  (restrictionIso R X).hom.naturality

variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R,
  (etaleRestriction (Compactification.Of.ι (object X))).op.HasLeftKanExtension F]

/-- Actual left-adjoint uniqueness along identity restriction, valid for Ring R. -/
def extensionIso : etaleExtensionByZero (Compactification.Of.ι (object X))
    (ModuleCat.{u + 1} R) ≅ 𝟭 (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Adjunction.leftAdjointUniq
    (etaleExtensionByZero_adjunction (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R))
    (Adjunction.id.ofNatIsoRight (restrictionIso R X).symm)

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Extension by zero along the identity compactification admits an injective resolution. -/
instance extension_hasInjectiveResolution : HasInjectiveResolution
    ((etaleExtensionByZero (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F) := by
  change HasInjectiveResolution (show Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R) from
    (etaleExtensionByZero (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F)
  infer_instance

/-- The actual resolution map induced by the identity-extension counit. -/
def map :
    NoncommGeometricSource.arithmeticCochain R X
      ((etaleExtensionByZero (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F) ⟶
    NoncommGeometricSource.arithmeticCochain R X F :=
  HomologicalComplex.extendMap
    (((NoncommGeometricSource.completedSections R X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc ((extensionIso R X).hom.app F)
        (injectiveResolution F)
        (injectiveResolution ((etaleExtensionByZero (Compactification.Of.ι (object X))
          (ModuleCat.{u + 1} R)).obj F)))) ComplexShape.embeddingUpNat

/-- Resolution comparison for an actual coefficient isomorphism is a homotopy
equivalence and remains so after geometric sections. -/
instance map_quasiIso : QuasiIso (map R X F) := sorry

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- The derived isomorphism induced by the resolution map of the identity-extension counit. -/
def derivedIso :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X
      ((etaleExtensionByZero (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F)) ≅
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X F) :=
  asIso (DerivedCategory.Q.map (map R X F))

end NoncommIdentityCompactification
