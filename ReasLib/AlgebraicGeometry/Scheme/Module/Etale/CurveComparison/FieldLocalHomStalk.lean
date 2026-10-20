module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldScalarStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomCoefficient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearHomStalk

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldLocalHomStalk
variable (k : Type u) [Field k]
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]
variable (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The same canonical field point, now bundled as a scheme geometric point. -/
def geometricPoint : GeometricPoint (Spec (CommRingCat.of k)) :=
  GeometricPoint.of (AlgebraicClosure k) (FieldModuleDescent.pointHom k)

/-- Read an actual right-linear Hom germ as an A-linear local-Hom germ,
using scalar/stalk compatibility and the identity-on-sections coefficient bridge. -/
def homGerm
    (α : ((FieldModuleDescent.forward k Rᵐᵒᵖ).obj
      (NoncommLocalHom.obj h hc (Spec (CommRingCat.of k)) F J)).obj.V) :=
  (((FieldModuleDescent.forward k A).map
    (NoncommLocalHomCoefficient.underlyingIso h hc (Spec (CommRingCat.of k)) F J).hom).hom.hom.hom)
      ((FieldScalarStalk.iso k (NoncommLocalHom.opScalarHom h hc)
        (NoncommLocalHom.obj h hc (Spec (CommRingCat.of k)) F J)).inv.hom α)

/-- Evaluate the actual Hom germ on the actual source germ, after the scalar
stalk identification. This reuses the established representative-evaluation map. -/
def evaluate
    (α : ((FieldModuleDescent.forward k Rᵐᵒᵖ).obj
      (NoncommLocalHom.obj h hc (Spec (CommRingCat.of k)) F J)).obj.V) :
    (NoncommLocalHom.modules h).obj ((FieldModuleDescent.forward k R).obj F).obj.V →ₗ[A]
      ((FieldModuleDescent.forward k A).obj J).obj.V :=
  (ActualLinearHomStalk.map A (geometricPoint k)
    ((NoncommLocalHom.sheaves h (Spec (CommRingCat.of k))).obj F) J (homGerm k h hc F J α)).comp
      (FieldScalarStalk.iso k h F).inv.hom

end FieldLocalHomStalk
