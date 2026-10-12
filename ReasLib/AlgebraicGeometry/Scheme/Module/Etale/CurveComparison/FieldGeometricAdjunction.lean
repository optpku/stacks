/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldModuleDescent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
noncomputable section
universe u

namespace FieldGeometricAdjunction
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable (X : SchemeOverField k) [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- The actual arithmetic direct image to the field's etale site. -/
def directImage := (smallEtalePullback X.hom).sheafPushforwardContinuous
  (ModuleCat.{u + 1} R) (Spec (.of k)).smallEtaleTopology X.left.smallEtaleTopology

/-- Pull a Galois module back via its concrete field sheaf. -/
def pullback := FieldModuleDescent.inverse k R ⋙ NoncommGeometricSource.modulePullback R X.hom

/-- The actual etale object over X obtained from a field-etale neighborhood. -/
abbrev pulledObject (U : (Spec (.of k)).Etale) := (smallEtalePullback X.hom).obj U

/-- The pointing over kbar gives a specified map from Xbar to that etale object. -/
def pointedLift (U : (Spec (.of k)).Etale) (x : (FieldModuleDescent.point k).fiber.obj U) :
    geometricBaseChange X ⟶ (pulledObject X U).left :=
  pullback.lift (FieldExtension.toBase k (AlgebraicClosure k) X.hom ≫ x.left)
    (geometricToArithmeticHom X) (by sorry)

/-- The same pointing as a section of the geometrically pulled-back etale object. -/
def pointedSection (U : (Spec (.of k)).Etale) (x : (FieldModuleDescent.point k).fiber.obj U) :
    globalEtale (geometricBaseChange X) ⟶
      (smallEtalePullback (geometricToArithmeticHom X)).obj (pulledObject X U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pointedLift X U x) (𝟙 (geometricBaseChange X)) (by sorry)) (by sorry)

/-- Pull a section through the actual inverse-image unit and then restrict
along the specified geometric section. -/
def sectionMap (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : (Spec (.of k)).Etale) (x : (FieldModuleDescent.point k).fiber.obj U) :
    ((directImage R X).obj F).obj.obj (op U) ⟶
      ((NoncommGeometricSource.sectionAction R X).obj F).V :=
  (((smallEtalePullback_sheafAdjunction (geometricToArithmeticHom X)
      (ModuleCat.{u + 1} R)).unit.app F).hom.app (op (pulledObject X U))) ≫
    ((NoncommGeometricSource.modulePullback R (geometricToArithmeticHom X)).obj F).obj.map
      (pointedSection X U x).op

/-- Actual filtered-stalk map from the arithmetic direct image to geometric sections. -/
def stalkMap (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    ((FieldModuleDescent.forward k R).obj ((directImage R X).obj F)).obj.V ⟶
      ((NoncommGeometricSource.sectionAction R X).obj F).V :=
  (FieldModuleDescent.point k).presheafFiberDesc (sectionMap R X F) (by sorry)

/-- Galois compatibility follows by moving the same pointing on both sides. -/
theorem stalkMap_equivariant (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))
    (σ : Gal(AlgebraicClosure k/k)) :
    (((FieldModuleDescent.forward k R).obj ((directImage R X).obj F)).obj.ρ σ) ≫ stalkMap R X F =
      stalkMap R X F ≫ ((NoncommGeometricSource.sectionAction R X).obj F).ρ σ := by sorry

/-- The comparison is the displayed section-pullback/stalk map, naturally in F. -/
def comparison : directImage R X ⋙ FieldModuleDescent.forward k R ⟶
    NoncommGeometricSource.discreteSections R X where
  app F := ObjectProperty.homMk { hom := stalkMap R X F, comm := stalkMap_equivariant R X F }
  naturality := by sorry

/-- Qcqs continuity makes this specified degree-zero base-change map invertible. -/
instance comparison_isIso : IsIso (comparison R X) := by sorry

/-- The geometric-sections adjunction is the field germ/evaluation adjunction
composed with actual etale pullback, then the specified base-change comparison. -/
def adjunction : pullback R X ⊣ NoncommGeometricSource.discreteSections R X :=
  Adjunction.ofNatIsoRight
    ((FieldModuleDescent.equivalence k R).symm.toAdjunction.comp
      (smallEtalePullback_sheafAdjunction X.hom (ModuleCat.{u + 1} R)))
    (@asIso _ _ _ _ (comparison R X) (comparison_isIso R X))

/-- Pointwise linear maps and exact module pullback make the concrete left adjoint additive. -/
instance pullback_additive : (pullback R X).Additive := by sorry

/-- Apply the actual germ/evaluation adjunction termwise to cochains. -/
def cochainAdjunction :=
  (adjunction R X).mapHomologicalComplexAdjunction (ComplexShape.up ℤ)

/-- Convert a specified Galois-equivariant section-complex map to its actual
arithmetic sheaf map. This is the bridge used by the enhanced evaluation. -/
def adjointCochainMap
    {P : CochainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℤ}
    {J : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ}
    (f : P ⟶ ((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) :
    ((pullback R X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ J :=
  ((cochainAdjunction R X).homEquiv P J).symm f

/-- Its components are the specified pullback map followed by the specified counit. -/
theorem adjointCochainMap_component
    {P : CochainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℤ}
    {J : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ}
    (f : P ⟶ ((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) (i : ℤ) :
    (adjointCochainMap R X f).f i = (pullback R X).map (f.f i) ≫
      (adjunction R X).counit.app (J.X i) := by sorry

/-- Explicit zero-extension comparison for actual arithmetic sheaf resolutions.
In nonnegative degree use the extension identifications; in negative degree use zero. -/
def sectionsExtensionMap
    (J : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ) :
    (((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J).extend ComplexShape.embeddingUpNat ⟶
    ((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (J.extend ComplexShape.embeddingUpNat) where
  f i := if h : 0 ≤ i then
      ((((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J).extendXIso ComplexShape.embeddingUpNat
          (i := i.toNat) (i' := i) (by simp [Int.toNat_of_nonneg h])).hom ≫
      (NoncommGeometricSource.discreteSections R X).map
        (J.extendXIso ComplexShape.embeddingUpNat
          (i := i.toNat) (i' := i) (by simp [Int.toNat_of_nonneg h])).inv
    else 0
  comm' := by sorry

/-- Apply the actual adjunction to a specified map into a resolution's sections.
No desired geometric comparison is supplied as existential data. -/
def adjointExtendedMap
    {P : CochainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℤ}
    (J : CochainComplex (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
    (f : P ⟶ (((NoncommGeometricSource.discreteSections R X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J).extend ComplexShape.embeddingUpNat) :
    ((pullback R X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      J.extend ComplexShape.embeddingUpNat :=
  adjointCochainMap R X (f ≫ sectionsExtensionMap R X J)

end FieldGeometricAdjunction
