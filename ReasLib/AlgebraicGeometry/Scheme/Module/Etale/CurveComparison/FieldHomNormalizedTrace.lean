/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomCochainComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomTargetComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualNormalizedRootsTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomTargetAcyclicity

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace FieldHomNormalizedTrace
variable {k : Type u} [Field k]
variable (n : ℕ) [hnzero : NeZero n]
variable {R : Type (u + 1)} [Ring R]
variable (h : ActualRootsModule.Coeff.{u} n →+* R)
variable (hc : ∀ (a : ActualRootsModule.Coeff.{u} n) (r : R), h a * r = r * h a)
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)) AddCommGrpCat.{u + 1})]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z)
  (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)),
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}), (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [HasDerivedCategory (DiscreteModuleCat (ActualRootsModule.Coeff.{u} n) Gal(AlgebraicClosure k/k))]
variable (hn : IsUnit (n : k))
variable (B : ChainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℕ)

abbrev rootsResolution := (injectiveResolution (ResidualNormalizedRootsTrace.compactRoots n X P)).cocomplex

def source := ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P.obj.right).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj (NoncommLocalHomComplex.shiftedComplex h hc P.obj.right.left
    (FieldHomCochainComparison.pulledB P.obj.right B) (rootsResolution n X P))

def injectiveTarget := ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommLocalHomComplex.shiftedComplex h hc (Spec (CommRingCat.of k))
    (FieldHomCochainComparison.fieldB B) (ResidualNormalizedRootsTrace.fieldInjectives (k := k) n))

/-- The target before resolving the trivial trace coefficient: actual field
local Hom into the degree-two single sheaf. Finiteness is needed only for its
later identification with the full finite character module. -/
def characterModel := ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (NoncommLocalHomComplex.shiftedComplex h hc (Spec (CommRingCat.of k))
    (FieldHomCochainComparison.fieldB B)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 2).obj (ResidualNormalizedRootsTrace.fieldTarget (k := k) n)))

/-- Postcompose with the SPECIFIED equivariant normalized trace representative,
after the actual geometric-Hom/field-Hom complex comparison. -/
def traceMap : source n h hc X P B ⟶ injectiveTarget n h hc B :=
  (FieldHomCochainComparison.shiftedIso h hc P.obj.right B (rootsResolution n X P)).hom ≫
  ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (LocalHomTargetComparison.shiftedMap h hc (Spec (CommRingCat.of k))
      (FieldHomCochainComparison.fieldB B) (ResidualNormalizedRootsTrace.cochainTrace n X P hn))

/-- Actual augmentation of the trace coefficient, applied to every Hom factor. -/
def characterMap : characterModel n h hc B ⟶ injectiveTarget n h hc B :=
  ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (LocalHomTargetComparison.shiftedMap h hc (Spec (CommRingCat.of k))
      (FieldHomCochainComparison.fieldB B) (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n))

include hnzero in
/-- The actual field-target augmentation is acyclic for these Hom columns:
at the geometric stalk its injective resolution contracts onto the regular
self-injective Z/n-module. Finite-Hom/stalk comparison and finite-diagonal
totalization transport that contraction to this specified map. Neither
source A-flatness nor injectivity of the trivial Galois object is asserted. -/
theorem characterMap_quasiIso (hB : ∀ i : ℕ, Finite (B.X i).obj.V) :
    QuasiIso (characterMap n h hc B) := by
  -- Local instance justification (proof-local temporary data): acyclicity is proved for the actual regular-coefficient augmentation, not arbitrary target quasi-isomorphisms.
  letI := FieldHomTargetAcyclicity.traceAugmentation_quasiIso.{u, u + 1} k n h hc B hB
  unfold characterMap
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ (FieldModuleDescent.forward k Rᵐᵒᵖ)

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj Rᵐᵒᵖ Gal(AlgebraicClosure k/k)))]

/-- Completed residual trace from actual geometric Hom to the finite character
model. Only the displayed trace-coefficient augmentation is inverted. -/
def completedTrace (hB : ∀ i : ℕ, Finite (B.X i).obj.V) :
    DerivedCategory.Q.obj (NoncommCompletedCochainTransport.cochain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
      (source n h hc X P B)) ⟶
    DerivedCategory.Q.obj (NoncommCompletedCochainTransport.cochain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
      (characterModel n h hc B)) :=
  -- Local instance justification (proof-local temporary data): this particular Hom augmentation is a quasi-isomorphism.
  letI := characterMap_quasiIso n h hc B hB
  DerivedCategory.Q.map
    (((NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (traceMap n h hc X P hn B)) ≫
  (@asIso _ _ _ _ (DerivedCategory.Q.map
    (((NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (characterMap n h hc B)))
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (HomologicalComplex.quasiIso_map_of_preservesHomology (characterMap n h hc B)
        (NoncommPointwiseCompletedAction.functor Rᵐᵒᵖ Gal(AlgebraicClosure k/k))))).inv

end FieldHomNormalizedTrace
