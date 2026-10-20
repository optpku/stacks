module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldModuleDescent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DiscreteScalarRestriction

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldScalarStalk
variable (k : Type u) [Field k]
variable {S T : Type (u + 1)} [Ring S] [Ring T] (h : S →+* T)
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars.{u + 1} h)]

instance restriction_preservesFiltered :
    PreservesFilteredColimitsOfSize.{u, u} (ModuleCat.restrictScalars.{u + 1} h) := by sorry

/-- Scalar restriction commutes with the ACTUAL field-point colimit. -/
def iso (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} T)) :
    ((FieldModuleDescent.forward k S).obj
      ((sheafCompose (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} h)).obj F)).obj.V ≅
    (ModuleCat.restrictScalars.{u + 1} h).obj ((FieldModuleDescent.forward k T).obj F).obj.V :=
  ((FieldModuleDescent.point k).presheafFiberCompIso
    (ModuleCat.restrictScalars h : ModuleCat.{u + 1} T ⥤ ModuleCat.{u + 1} S)).app F.obj

/-- The same scalar/stalk comparison with its actual field-point action.
Each group map is induced by the same point-fiber natural automorphism. -/
def discreteIso (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} T)) :
    (FieldModuleDescent.forward k S).obj
      ((sheafCompose (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} h)).obj F) ≅
    (DiscreteScalarRestriction.functor h Gal(AlgebraicClosure k/k)).obj ((FieldModuleDescent.forward k T).obj F) :=
  ObjectProperty.isoMk _ (Action.mkIso (iso k h F) (fun _ ↦ by sorry))

end FieldScalarStalk
