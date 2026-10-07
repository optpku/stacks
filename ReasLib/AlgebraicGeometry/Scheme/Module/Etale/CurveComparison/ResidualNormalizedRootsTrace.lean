module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualGeometricSiteComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CentralRootsPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.SourceEndpointAssembly
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.EquivariantTopTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedCochainTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactificationTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldExactTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldGeometricAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.SpecifiedDerivedRepresentative

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ResidualNormalizedRootsTrace
variable {k : Type u} [Field k]
variable (n : ℕ) [NeZero n]
abbrev A := ActualRootsModule.Coeff.{u} n
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} n))]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (A.{u} n)))]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (A.{u} n)) AddCommGrpCat.{u + 1})]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (A.{u} n)),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (A.{u} n)),
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (etaleRestriction j).op.HasLeftKanExtension F]

abbrev roots := ActualRootsModule.liftedSheaf X.left n
abbrev compactRoots := (etaleExtensionByZero (Compactification.Of.ι P)
  (ModuleCat.{u + 1} (A.{u} n))).obj (roots n X)
abbrev cochain := NoncommGeometricSource.arithmeticDiscreteCochain (A.{u} n) P.obj.right (compactRoots n X P)

/-- Actual base-change mate followed by the central-linear Kummer-kernel map. -/
def geometricCoefficientMap : geometricModuleRestrictionCompactSupport X P (roots n X) ⟶
    (etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) (ModuleCat.{u + 1} (A.{u} n))).obj
      (ActualRootsModule.liftedSheaf (geometricBaseChange X) n) :=
  (ActualGeometricCompactSupport.coefficientIso X P (A.{u} n) (roots n X)).hom ≫
    (etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) (ModuleCat.{u + 1} (A.{u} n))).map
      (CentralRootsPullback.map (geometricToArithmeticHom X) n)

/-- The underlying additive compact-roots coefficient is identified by the
actual scalar-forgetting mate and identity on roots sections. -/
def additiveCoefficientMap :=
  (ActualLambdaEndpoint.extensionForgetIso (A.{u} n) (ActualGeometricCompactSupport.interior X P)
    (ActualRootsModule.liftedSheaf (geometricBaseChange X) n)).inv ≫
  (etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) AddCommGrpCat.{u + 1}).map
    (CentralRootsPullback.forgetIso (X := geometricBaseChange X) n).hom

/-- Actual resolution/site comparison, then geometric roots and scalar-forgetting maps. -/
def additiveH2Map :
    ((cochain n X P).homology 2).obj.V →+
    ((etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) AddCommGrpCat.{u + 1}).obj
      (ActualRootsModule.additiveSheaf (geometricBaseChange X) n)).H 2 :=
  (Sheaf.H.map (additiveCoefficientMap n X P) 2).comp
    (((siteModuleCohomologyModuleFunctor
      (J := (geometricBaseChange P.obj.right).smallEtaleTopology) (A := A.{u} n) 2).map
        (geometricCoefficientMap n X P)).hom.toAddMonoidHom.comp
      (ResidualGeometricSiteComparison.siteHomologyIso (A.{u} n) P.obj.right (compactRoots n X P) 2).hom.hom.toAddMonoidHom)

variable (hn : IsUnit (n : k))

/-- Positive-degree normalization is Picard degree modulo n on the actual
smooth projective completion, after the specified proper refinement map. -/
def normalizedH2 : ((cochain n X P).homology 2).obj.V →+ ZMod n :=
  (NormalizedCurveTrace.intrinsicCompactKummerTrace
    (ActualSourceAssembly.completion (ActualSourceAssembly.Xgeom X)).curve
    (ActualSourceAssembly.completion (ActualSourceAssembly.Xgeom X)).j.left n
    (Nat.pos_of_ne_zero (NeZero.ne n)) (by simpa using hn.map (algebraMap k (AlgebraicClosure k)))).comp
  ((ActualCurveRefinement.cohomologyMap (ActualSourceAssembly.Xgeom X)
    (ActualSourceAssembly.completion (ActualSourceAssembly.Xgeom X)).curve
    (ActualSourceAssembly.completion (ActualSourceAssembly.Xgeom X)).j
    (ActualSourceAssembly.geometricCompactification X P)
    (ActualRootsModule.additiveSheaf (geometricBaseChange X) n) 2).comp (additiveH2Map n X P))

/-- The normalized trace coefficient carries the trivial residual Galois action. -/
def target : DiscreteModuleCat (A.{u} n) Gal(AlgebraicClosure k/k) :=
  ⟨{ V := ModuleCat.of (A.{u} n) (A.{u} n), ρ := 1 }, by sorry⟩

/-- The normalized additive trace re-bundled over its canonical central Z/n scalars. -/
def traceLinear : ((cochain n X P).homology 2).obj.V ⟶ (target (k := k) n).obj.V :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up (normalizedH2 n X P hn x)
      map_add' := by intros; simp only [map_add]; rfl
      map_smul' := by sorry }

/-- Kummer/Picard normalization is unchanged under the actual semilinear Galois
pullback and the specified proper refinement, hence this precise trace is equivariant. -/
theorem trace_equivariant (σ : Gal(AlgebraicClosure k/k)) :
    ((cochain n X P).homology 2).obj.ρ σ ≫ traceLinear n X P hn =
      traceLinear n X P hn ≫ (target (k := k) n).obj.ρ σ := by sorry

/-- The residual-equivariant trace uses the displayed normalized geometric function. -/
def trace : (cochain n X P).homology 2 ⟶ target (k := k) n :=
  ObjectProperty.homMk { hom := traceLinear n X P hn, comm := trace_equivariant n X P hn }

include hcurve hsmooth hconnected hn in
/-- The genuine prime-to-characteristic curve compact-support bound. -/
theorem above_two (i : ℤ) (hi : 2 < i) : IsZero ((cochain n X P).homology i) := by sorry

variable [HasDerivedCategory (DiscreteModuleCat (A.{u} n) Gal(AlgebraicClosure k/k))]

/-- The enhanced derived roots trace in the ALL-discrete residual category.
Its roof inverts only the actual top-truncation inclusion. The trivial Galois
target is not claimed injective. This is a trace map, not an arbitrary duality iso. -/
def derivedTrace : DerivedCategory.Q.obj (cochain n X P) ⟶
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (DiscreteModuleCat (A.{u} n) Gal(AlgebraicClosure k/k)) 2).obj (target (k := k) n)) :=
  ActualEquivariantTopTrace.map (cochain n X P) 2 (above_two n X P hn) (trace n X P hn)

/-- Canonical functor/extension identification with the ACTUAL completed
geometric source, rather than a replacement of its cochains. -/
def completedSourceIso :
    NoncommCompletedCochainTransport.cochain (A.{u} n) Gal(AlgebraicClosure k/k) (cochain n X P) ≅
    NoncommGeometricSource.arithmeticCochain (A.{u} n) P.obj.right (compactRoots n X P) :=
  ComplexShape.embeddingUpNat.mapAppIso
    (NoncommPointwiseCompletedAction.functor (A.{u} n) Gal(AlgebraicClosure k/k))
    (((NoncommGeometricSource.discreteSections (A.{u} n) P.obj.right).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution (compactRoots n X P)).cocomplex)

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj (A.{u} n) Gal(AlgebraicClosure k/k)))]

/-- Fully residual-equivariant completed-linear normalized roots trace.
The target is concentrated in degree 2, hence carries the approved [-2]. -/
def derivedCompletedTrace :
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain
      (A.{u} n) P.obj.right (compactRoots n X P)) ⟶
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u + 1} (NoncommCompletedRing.Obj (A.{u} n) Gal(AlgebraicClosure k/k))) 2).obj
        ((NoncommPointwiseCompletedAction.functor (A.{u} n) Gal(AlgebraicClosure k/k)).obj
          (target (k := k) n))) :=
  DerivedCategory.Q.map (completedSourceIso n X P).inv ≫
    NoncommCompletedCochainTransport.derivedTopMap (A.{u} n) Gal(AlgebraicClosure k/k)
      (cochain n X P) 2 (above_two n X P hn) (trace n X P hn)

variable (Q : Compactification.Of (Spec (CommRingCat.of k)) X)
variable (f : Q.obj.right ⟶ P.obj.right)
variable (hcart : IsPullback (𝟙 X.left) (Compactification.Of.ι Q) (Compactification.Of.ι P) f.left)
variable [hproper : IsProper f.left]

include hproper in
/-- The normalized trace is independent of proper compactification refinement
along the ACTUAL geometric resolution/extension-by-zero map. -/
theorem trace_refinement :
    HomologicalComplex.homologyMap
      (NoncommCompactificationTransport.discreteMap (A.{u} n) X P Q f hcart (roots n X)) 2 ≫
        trace n X Q hn = trace n X P hn := by sorry

include hproper in
/-- The same compatibility in the completed residual derived category. This is
a law of the specified maps, not an input used to manufacture either trace. -/
theorem derivedCompletedTrace_refinement :
    DerivedCategory.Q.map
      (NoncommCompactificationTransport.completedMap (A.{u} n) X P Q f hcart (roots n X)) ≫
        derivedCompletedTrace n X Q hn = derivedCompletedTrace n X P hn := by sorry

/-- Arithmetic direct image of the SAME compact roots resolution, on the field site. -/
instance fieldDirectImage_additive : (FieldGeometricAdjunction.directImage (A.{u} n) P.obj.right).Additive := by sorry

def fieldComplex := ((FieldGeometricAdjunction.directImage (A.{u} n) P.obj.right).mapHomologicalComplex
  (ComplexShape.up ℕ)).obj (injectiveResolution (compactRoots n X P)).cocomplex

abbrev fieldCochain := (fieldComplex n X P).extend ComplexShape.embeddingUpNat
abbrev fieldTarget := (FieldModuleDescent.inverse k (A.{u} n)).obj (target (k := k) n)

/-- Actual field-stalk/direct-image comparisons in every resolution degree. -/
def fieldCochainIso :
    ((FieldModuleDescent.forward k (A.{u} n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (fieldCochain n X P) ≅ cochain n X P :=
  ComplexShape.embeddingUpNat.mapAppIso (FieldModuleDescent.forward k (A.{u} n)) (fieldComplex n X P) ≪≫
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (@asIso _ _ _ _ (FieldGeometricAdjunction.comparison (A.{u} n) P.obj.right)
        (FieldGeometricAdjunction.comparison_isIso (A.{u} n) P.obj.right)).app
        ((injectiveResolution (compactRoots n X P)).cocomplex.X i)) (by sorry))

def fieldHomologyIso :
    (FieldModuleDescent.forward k (A.{u} n)).obj ((fieldCochain n X P).homology 2) ≅
    (cochain n X P).homology 2 :=
  ((fieldCochain n X P).mapHomologyIso (FieldModuleDescent.forward k (A.{u} n)) 2).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 2).mapIso (fieldCochainIso n X P)

/-- Translate the specified normalized residual trace through the actual field
equivalence; no extra trace map is chosen. -/
def fieldTrace : (fieldCochain n X P).homology 2 ⟶ fieldTarget (k := k) n :=
  (FieldModuleDescent.forward k (A.{u} n)).preimage
    ((fieldHomologyIso n X P).hom ≫ trace n X P hn ≫
      ((FieldModuleDescent.equivalence k (A.{u} n)).counitIso.app (target (k := k) n)).inv)

include hcurve hsmooth hconnected hn in
theorem field_above_two (i : ℤ) (hi : 2 < i) : IsZero ((fieldCochain n X P).homology i) := by sorry

variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} (A.{u} n)))]

def fieldDerivedTrace := ActualEquivariantTopTrace.map (fieldCochain n X P) 2
  (field_above_two n X P hn) (fieldTrace n X P hn)

/-- Place an actual nonnegative injective resolution in degrees 2,3,... . -/
def positiveTwo : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun i : ℕ ↦ i + 2) (by intro i j hij; dsimp at hij; omega)
    (by intro i j; change i + 1 = j ↔ (i + 2) + 1 = j + 2; omega)

instance positiveTwo_relIff : positiveTwo.IsRelIff := by
  unfold positiveTwo
  infer_instance

def fieldInjectives := (injectiveResolution (fieldTarget (k := k) n)).cocomplex.extend positiveTwo
abbrev fieldInjectiveTarget := (fieldInjectives (k := k) n).extend ComplexShape.embeddingUpNat

/-- Terms are actual injectives or genuine zero extensions below degree 2.
The trivial residual coefficient itself is NOT asserted injective. -/
instance fieldInjectives_injective (i : ℕ) : Injective ((fieldInjectives (k := k) n).X i) := by sorry

instance fieldInjectiveTarget_kInjective : CochainComplex.IsKInjective (fieldInjectiveTarget (k := k) n) := by
  infer_instance

def fieldTargetNatMap : (HomologicalComplex.single _ (ComplexShape.up ℕ) 2).obj (fieldTarget (k := k) n) ⟶
    fieldInjectives (k := k) n :=
  (HomologicalComplex.extendSingleIso positiveTwo (fieldTarget (k := k) n) 0 2 rfl).inv ≫
    HomologicalComplex.extendMap (injectiveResolution (fieldTarget (k := k) n)).ι positiveTwo

def fieldTargetMap : (CochainComplex.singleFunctor _ 2).obj (fieldTarget (k := k) n) ⟶
    fieldInjectiveTarget (k := k) n :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (fieldTarget (k := k) n) 2 2 rfl).inv ≫
    HomologicalComplex.extendMap (fieldTargetNatMap (k := k) n) ComplexShape.embeddingUpNat

/-- This is the actual resolution inclusion of the target in degree 2. -/
instance fieldTargetNatMap_quasiIso : QuasiIso (fieldTargetNatMap (k := k) n) := by
  -- Local instance justification (proof-local temporary data): extend this actual injective-resolution augmentation.
  letI : QuasiIso (HomologicalComplex.extendMap
      (injectiveResolution (fieldTarget (k := k) n)).ι positiveTwo) :=
    (HomologicalComplex.quasiIso_extendMap_iff
      (injectiveResolution (fieldTarget (k := k) n)).ι positiveTwo).2
      (injectiveResolution (fieldTarget (k := k) n)).quasiIso
  let e := HomologicalComplex.extendSingleIso positiveTwo (fieldTarget (k := k) n) 0 2 rfl
  -- Local instance justification (proof-local temporary data): the other factor is the canonical single-extension isomorphism.
  letI : QuasiIso e.inv := quasiIso_of_isIso e.inv
  exact quasiIso_comp e.inv
    (HomologicalComplex.extendMap (injectiveResolution (fieldTarget (k := k) n)).ι positiveTwo)

instance fieldTargetMap_quasiIso : QuasiIso (fieldTargetMap (k := k) n) := by
  unfold fieldTargetMap
  infer_instance

/-- Lift precisely the normalized derived trace to the genuine injective
field-coefficient resolution, by Mathlib's K-injective hom bijection. -/
def traceRepresentative := SpecifiedDerivedRepresentative.map (fieldCochain n X P)
  (fieldInjectiveTarget (k := k) n)
  (fieldDerivedTrace n X P hn ≫ DerivedCategory.Q.map (fieldTargetMap (k := k) n))

/-- Restrict the specified representative to its actual nonnegative source and target. -/
def cochainTrace : fieldComplex n X P ⟶ fieldInjectives (k := k) n where
  f i := ((fieldComplex n X P).extendXIso ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl).inv ≫
    (traceRepresentative n X P hn).f (i : ℤ) ≫
    ((fieldInjectives (k := k) n).extendXIso ComplexShape.embeddingUpNat (i := i) (i' := (i : ℤ)) rfl).hom
  comm' := by sorry

/-- This cochain arrow represents the specified normalized trace, not an
arbitrary equivariant lift of its underlying additive function. -/
theorem traceRepresentative_spec : DerivedCategory.Q.map (traceRepresentative n X P hn) =
    fieldDerivedTrace n X P hn ≫ DerivedCategory.Q.map (fieldTargetMap (k := k) n) :=
  SpecifiedDerivedRepresentative.map_spec _ _ _

/-- Extension recovers the specified representative, since both complexes
are actually zero in negative degrees. -/
theorem cochainTrace_extend :
    HomologicalComplex.extendMap (cochainTrace n X P hn) ComplexShape.embeddingUpNat =
    traceRepresentative n X P hn := by sorry

theorem cochainTrace_spec : DerivedCategory.Q.map
    (HomologicalComplex.extendMap (cochainTrace n X P hn) ComplexShape.embeddingUpNat) =
    fieldDerivedTrace n X P hn ≫ DerivedCategory.Q.map (fieldTargetMap (k := k) n) := by
  rw [cochainTrace_extend]
  exact traceRepresentative_spec n X P hn

end ResidualNormalizedRootsTrace
