module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommAssociatedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualCompletedTarget

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
noncomputable section
universe u

namespace NoncommResidualSectionsComparison
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))

abbrev G := Aut (standardFiniteEtaleFiber η)
abbrev Γ := Aut (standardFiniteEtaleFiber (arithmeticPoint X η))
abbrev Q := ActualResidualCompletedTarget.residualGroup X η

/-- The all-discrete relative invariants for the actual fundamental exact sequence. -/
abbrev invariants := NoncommResidualInvariants.functor R (G X η) (Γ X η) (Q X η)
  (geometricToArithmetic X η).hom (arithmeticToGalois X (arithmeticPoint X η)).hom
  (geometricToArithmetic_range_eq_arithmeticToGalois_ker X η)
  (arithmeticToGalois_surjective X (arithmeticPoint X η))

/-- Rename the actual field-Galois action by its specified continuous fiber-group equivalence. -/
def toResidual : DiscreteModuleCat R Gal(AlgebraicClosure k/k) ⥤ DiscreteModuleCat R (Q X η) where
  obj M := ⟨(Action.res (ModuleCat.{u + 1} R) (ActualResidualCompletedTarget.residualEquiv X η).toMonoidHom).obj
    M.obj, by sorry⟩
  map f := ObjectProperty.homMk
    ((Action.res (ModuleCat.{u + 1} R) (ActualResidualCompletedTarget.residualEquiv X η).toMonoidHom).map f.hom)
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance toResidual_additive : (toResidual R X η).Additive := by sorry
instance toResidual_preservesHomology : (toResidual R X η).PreservesHomology := by sorry

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]

def sheafSections := NoncommGeometricSource.discreteSections R X ⋙ toResidual R X η
def realizedSections := functor (Λ := R) (xbar := arithmeticPoint X η) ⋙ sheafSections R X η

/-- Actual finite-stage base change, then the published germ-counit vector map. -/
def sectionVector (M : DiscreteModuleCat R (Γ X η)) :
    ((realizedSections R X η).obj M).obj.V ⟶ M.obj.V :=
  (NoncommGeometricSource.sections R).map
    (NoncommAssociatedBaseChange.baseChangeMap R (geometricToArithmeticHom X) η M) ≫
  NoncommAssociatedSections.sectionVector R η
    ((NoncommAssociatedBaseChange.restriction R (geometricToArithmeticHom X) η).obj M)

/-- Geometric monodromy fixes the specified global-section germ. -/
theorem sectionVector_fixed (M : DiscreteModuleCat R (Γ X η))
    (s : ((realizedSections R X η).obj M).obj.V) (g : G X η) :
    (M.obj.ρ ((geometricToArithmetic X η).hom g)).hom ((sectionVector R X η M).hom s) =
      (sectionVector R X η M).hom s := by sorry

/-- The literal germ vector, bundled in the correct invariant submodule. -/
def invariantMap (M : DiscreteModuleCat R (Γ X η)) :
    ((realizedSections R X η).obj M).obj.V ⟶ ((invariants R X η).obj M).obj.V :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(sectionVector R X η M).hom s, sectionVector_fixed R X η M s⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }

/-- Actual geometric Galois pullback agrees with arithmetic lifts on the same germs. -/
theorem invariantMap_equivariant (M : DiscreteModuleCat R (Γ X η)) (q : Q X η) :
    ((realizedSections R X η).obj M).obj.ρ q ≫ invariantMap R X η M =
    invariantMap R X η M ≫ ((invariants R X η).obj M).obj.ρ q := by sorry

def comparison : realizedSections R X η ⟶ invariants R X η where
  app M := ObjectProperty.homMk { hom := invariantMap R X η M, comm := invariantMap_equivariant R X η M }
  naturality := by sorry

/-- Germ evaluation bijects geometric sections with invariant vectors, including
the independently constructed residual action. -/
instance comparison_isIso : IsIso (comparison R X η) := by sorry

def iso : realizedSections R X η ≅ invariants R X η :=
  @asIso _ _ _ _ (comparison R X η) (comparison_isIso R X η)

end NoncommResidualSectionsComparison
