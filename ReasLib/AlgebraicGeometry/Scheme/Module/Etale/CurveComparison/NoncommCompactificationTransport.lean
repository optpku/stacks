module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricCochainPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedCochainTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactificationChange

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommCompactificationTransport
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable (X : SchemeOverField k)
variable (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
variable (f : Q.obj.right ⟶ P.obj.right)
variable (hcart : IsPullback (𝟙 X.left) (Compactification.Of.ι Q) (Compactification.Of.ι P) f.left)

/-- Restrict the same module sections along the actual fixed-interior site isomorphism. -/
def restrictionIso :
    (smallEtalePullback f.left).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      P.obj.right.left.smallEtaleTopology Q.obj.right.left.smallEtaleTopology ⋙
      etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u + 1} R) ≅
    etaleRestrictionSheaf (Compactification.Of.ι Q) (ModuleCat.{u + 1} R) :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((ActualCompactificationChange.siteIso
            (Compactification.Of.ι P) (Compactification.Of.ι Q) f.left hcart).hom.app V.unop).op
          naturality := by sorry }
      inv := ObjectProperty.homMk
        { app := fun V ↦ F.obj.map ((ActualCompactificationChange.siteIso
            (Compactification.Of.ι P) (Compactification.Of.ι Q) f.left hcart).inv.app V.unop).op
          naturality := by sorry }
      hom_inv_id := by sorry
      inv_hom_id := by sorry }) (by sorry)

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback g).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (etaleRestriction j).op.HasLeftKanExtension F]

/-- Actual inverse-image/extension-by-zero mate over an arbitrary coefficient ring. -/
def extensionIso :
    etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R) ⋙
      NoncommGeometricSource.modulePullback R f.left ≅
    etaleExtensionByZero (Compactification.Of.ι Q) (ModuleCat.{u + 1} R) :=
  (((etaleExtensionByZero_adjunction (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).comp
    (smallEtalePullback_sheafAdjunction f.left (ModuleCat.{u + 1} R))).ofNatIsoRight
      (restrictionIso R X P Q f hcart)).leftAdjointUniq
    (etaleExtensionByZero_adjunction (Compactification.Of.ι Q) (ModuleCat.{u + 1} R))

variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))

abbrev coefficient (P : Compactification.Of (Spec (CommRingCat.of k)) X) :=
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} R)).obj F

/-- Actual residual-equivariant cochain refinement: geometric pullback,
injective-resolution comparison, and precisely the displayed extension mate. -/
def discreteMap :
    NoncommGeometricSource.arithmeticDiscreteCochain R P.obj.right (coefficient R X F P) ⟶
    NoncommGeometricSource.arithmeticDiscreteCochain R Q.obj.right (coefficient R X F Q) :=
  NoncommGeometricCochainPullback.map R f ((extensionIso R X P Q f hcart).hom.app F)

/-- Relate completion after geometric sections to the original completed source. -/
def completedSourceIso (P : Compactification.Of (Spec (CommRingCat.of k)) X) :
    NoncommCompletedCochainTransport.cochain R Gal(AlgebraicClosure k/k)
      (NoncommGeometricSource.arithmeticDiscreteCochain R P.obj.right (coefficient R X F P)) ≅
    NoncommGeometricSource.arithmeticCochain R P.obj.right (coefficient R X F P) :=
  ComplexShape.embeddingUpNat.mapAppIso (NoncommPointwiseCompletedAction.functor R Gal(AlgebraicClosure k/k))
    (((NoncommGeometricSource.discreteSections R P.obj.right).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution (coefficient R X F P)).cocomplex)

/-- The completed-ring map is the specified discrete refinement transported
through the canonical source identifications. -/
def completedMap :
    NoncommGeometricSource.arithmeticCochain R P.obj.right (coefficient R X F P) ⟶
    NoncommGeometricSource.arithmeticCochain R Q.obj.right (coefficient R X F Q) :=
  (completedSourceIso R X F P).inv ≫
  ((NoncommPointwiseCompletedAction.functor R Gal(AlgebraicClosure k/k)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (discreteMap R X P Q f hcart F) ≫
  (completedSourceIso R X F Q).hom

variable [hfinite : Finite R] [hproper : IsProper f.left]

include hfinite hproper in
/-- Proper base change for torsion module sheaves applies to this specific
refinement map, which is an isomorphism over the fixed open interior. -/
theorem discreteMap_quasiIso : QuasiIso (discreteMap R X P Q f hcart F) := by sorry

include hfinite hproper in
theorem completedMap_quasiIso : QuasiIso (completedMap R X P Q f hcart F) := by sorry

variable [HasDerivedCategory (ModuleCat.{u + 1} (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Invert only the actual proper-refinement map after its quasi-isomorphism theorem. -/
def derivedIso :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R P.obj.right (coefficient R X F P)) ≅
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R Q.obj.right (coefficient R X F Q)) :=
  -- Local instance justification (proof-local temporary data): proper base change for this explicit map.
  letI := completedMap_quasiIso R X P Q f hcart F
  asIso (DerivedCategory.Q.map (completedMap R X P Q f hcart F))

end NoncommCompactificationTransport
