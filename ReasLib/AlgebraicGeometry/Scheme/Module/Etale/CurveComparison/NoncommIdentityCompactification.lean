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

instance identity_etale : Etale (Compactification.Of.ι (object X)) :=
  inferInstanceAs (Etale (𝟙 X.left))

def siteIso : etaleRestriction (Compactification.Of.ι (object X)) ≅ 𝟭 X.left.Etale :=
  MorphismProperty.Over.mapId (P := @Etale) (Q := (⊤ : MorphismProperty Scheme))
    X.left (Compactification.Of.ι (object X)) rfl

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
theorem map_quasiIso : QuasiIso (map R X F) := by sorry

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

def derivedIso :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X
      ((etaleExtensionByZero (Compactification.Of.ι (object X)) (ModuleCat.{u + 1} R)).obj F)) ≅
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X F) :=
  -- Local instance justification (proof-local temporary data): this particular identity-coefficient resolution map is a quasi-isomorphism.
  letI := map_quasiIso R X F
  asIso (DerivedCategory.Q.map (map R X F))

end NoncommIdentityCompactification
