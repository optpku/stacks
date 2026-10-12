/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalRankLocus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.CellSheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# The actual global Q from the original perfect representative

Start from the representative and isomorphism that already belong to hE.
Construct the explicit cell replacement on X, pull its actual complex along
b followed by p, and apply the underived sheaf eta kernel construction.
No derived-eta localization, resolution-existence selector or newly chosen Q
occurs in this data path. The geometric/flat comparison laws remain explicit.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped RingedSpace.Hom
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)
  [IsEffectiveCartierDivisor D.subschemeι]

/-- The displayed cell replacement of the representative in the original hE. -/
def originalCellModel : CochainComplex X.toRingedSpace.Modules ℤ :=
  RingedSpace.CellReplacement.model (representative E hE)

def originalCellAugmentation : originalCellModel E hE ⟶ representative E hE :=
  RingedSpace.CellReplacement.augmentation (representative E hE)

instance originalCellAugmentation_quasiIso : QuasiIso (originalCellAugmentation E hE) :=
  RingedSpace.CellReplacement.augmentation_quasiIso (representative E hE)

/-- This comparison retains the original representationIso and the actual
cell augmentation. Only the image of that fixed quasi-isomorphism is inverted. -/
def originalCellComparison : (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
    (originalCellModel E hE) ≅ E :=
  RingedSpace.CellReplacement.comparison (representative E hE) ≪≫
    (representationIso E hE).symm

/-- The actual module pullback functor along the constructed map to X. -/
def graphModulePullback : X.toRingedSpace.Modules ⥤ (globalW E hE p D).toRingedSpace.Modules :=
  RingedSpace.Hom.pullback (globalB E hE p D ≫ p).toShHom

/-- Additivity is a property of the displayed ordinary pullback. -/
instance graphModulePullback_additive : (graphModulePullback E hE p D).Additive := by
  unfold graphModulePullback
  infer_instance

def graphCellModel : CochainComplex (globalW E hE p D).toRingedSpace.Modules ℤ :=
  ((graphModulePullback E hE p D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (originalCellModel E hE)

/-- The pulled-back actual Cartier ideal. -/
abbrev graphEtaIdeal := (globalDivisor E hE p D).toSubobject

/-- The specified effective Cartier ideal is invertible. This fixed-object
law supplies integral powers; it does not choose a divisor or complex. -/
instance graphEtaIdeal_invertible :
    isInvertibleObject (graphEtaIdeal E hE p D : (globalW E hE p D).toRingedSpace.Modules) := by
  sorry

/-- Each cell layer has flat stalks; the tower is a termwise split extension
of such layers and its filtered colimit is flat. Ordinary pullback preserves
flat terms, so the specified Cartier ideal acts monomorphically termwise. -/
instance graphCellModel_actionMono :
    RingedSpace.IdealSheaf.IsActionMono.Complex (graphEtaIdeal E hE p D)
      (graphCellModel E hE p D) := by
  sorry

/-- The actual eta complex: the kernel/differential construction on the
explicit pulled-back cell model, in all integer degrees. -/
def globalEtaComplex : CochainComplex (globalW E hE p D).toRingedSpace.Modules ℤ :=
  RingedSpace.IdealSheaf.Eta.complex (graphEtaIdeal E hE p D) (graphCellModel E hE p D)

/-- The global Q is the localization of this specific, constructed eta complex. -/
def globalQ : RingedSpace.ModuleDerived (globalW E hE p D).toRingedSpace :=
  DerivedCategory.Q.obj (globalEtaComplex E hE p D)

theorem globalQ_formula : globalQ E hE p D =
    DerivedCategory.Q.obj (globalEtaComplex E hE p D) := rfl

theorem graphCellModel_d (n m : ℤ) :
    (graphCellModel E hE p D).d n m =
      (graphModulePullback E hE p D).map ((originalCellModel E hE).d n m) := rfl

theorem originalCellComparison_hom :
    (originalCellComparison E hE).hom =
      (DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
        (originalCellAugmentation E hE) ≫ (representationIso E hE).inv := rfl

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
