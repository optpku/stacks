/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.MappedResolutionComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommGeometricCochainPullback
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback g).op.HasLeftKanExtension F]
variable {C D : SchemeOverField k} (f : D ⟶ C)
variable [CompactSpace C.left] [QuasiSeparatedSpace C.left]
variable [CompactSpace D.left] [QuasiSeparatedSpace D.left]

/-- The actual geometric base-change of the arithmetic over-field morphism. -/
def geometricMap : geometricBaseChange D ⟶ geometricBaseChange C :=
  pullback.map D.hom (FieldExtension.specMap k (AlgebraicClosure k))
    C.hom (FieldExtension.specMap k (AlgebraicClosure k)) f.left (𝟙 _) (𝟙 _)
    (by simpa using f.w.symm) (by simp)

theorem square : geometricMap f ≫ geometricToArithmeticHom C =
    geometricToArithmeticHom D ≫ f.left := by sorry

/-- Pullback compositors for the actual cartesian geometric/arithmetic square. -/
def coefficientIso (F : Sheaf C.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (NoncommGeometricSource.modulePullback R (geometricMap f)).obj
      ((NoncommGeometricSource.modulePullback R (geometricToArithmeticHom C)).obj F) ≅
    (NoncommGeometricSource.modulePullback R (geometricToArithmeticHom D)).obj
      ((NoncommGeometricSource.modulePullback R f.left).obj F) :=
  (NoncommGeometricSource.modulePullbackComp R (geometricToArithmeticHom C) (geometricMap f)).app F ≪≫
  (eqToIso (congrArg (fun h ↦ NoncommGeometricSource.modulePullback R h) (square f))).app F ≪≫
  ((NoncommGeometricSource.modulePullbackComp R f.left (geometricToArithmeticHom D)).app F).symm

/-- Actual section pullback followed by the displayed geometric compositor. -/
def sectionMap (F : Sheaf C.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (NoncommGeometricSource.sectionsPullback R (geometricMap f)).app
    ((NoncommGeometricSource.modulePullback R (geometricToArithmeticHom C)).obj F) ≫
  (NoncommGeometricSource.sections R).map (coefficientIso R f F).hom

/-- Arithmetic pullback commutes with the independent geometric Galois action. -/
def sectionsComparison : NoncommGeometricSource.discreteSections R C ⟶
    NoncommGeometricSource.modulePullback R f.left ⋙ NoncommGeometricSource.discreteSections R D where
  app F := ObjectProperty.homMk { hom := sectionMap R f F, comm := fun _ ↦ by sorry }
  naturality := by sorry

instance pullback_additive : (NoncommGeometricSource.modulePullback R f.left).Additive := by sorry
instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (NoncommGeometricSource.modulePullback R f.left) := by sorry
instance pullback_preservesFiniteColimits :
    PreservesFiniteColimits (NoncommGeometricSource.modulePullback R f.left) := by sorry

variable [EnoughInjectives (Sheaf C.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [EnoughInjectives (Sheaf D.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable {F : Sheaf C.left.smallEtaleTopology (ModuleCat.{u + 1} R)}
variable {F' : Sheaf D.left.smallEtaleTopology (ModuleCat.{u + 1} R)}
variable (a : (NoncommGeometricSource.modulePullback R f.left).obj F ⟶ F')

/-- Pull back the source resolution, use its explicit recursive injective
comparison, then descend the supplied coefficient morphism. -/
def resolutionMap :=
  ActualMappedResolution.map (NoncommGeometricSource.modulePullback R f.left)
    (injectiveResolution F)
    (injectiveResolution ((NoncommGeometricSource.modulePullback R f.left).obj F)) ≫
  InjectiveResolution.desc a (injectiveResolution F')
    (injectiveResolution ((NoncommGeometricSource.modulePullback R f.left).obj F))

/-- The specified section and resolution maps in each nonnegative degree. -/
def nonnegativeMap :
    ((NoncommGeometricSource.discreteSections R C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex ⟶
    ((NoncommGeometricSource.discreteSections R D).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F').cocomplex where
  f i := (sectionsComparison R f).app ((injectiveResolution F).cocomplex.X i) ≫
    (NoncommGeometricSource.discreteSections R D).map ((resolutionMap R f a).f i)
  comm' := by sorry

/-- Full residual-equivariant geometric cochain pullback; no derived isomorphism
or desired comparison map is selected as data. -/
def map : NoncommGeometricSource.arithmeticDiscreteCochain R C F ⟶
    NoncommGeometricSource.arithmeticDiscreteCochain R D F' :=
  HomologicalComplex.extendMap (nonnegativeMap R f a) ComplexShape.embeddingUpNat

end NoncommGeometricCochainPullback
