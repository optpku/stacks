module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ContinuousCompletedRingTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCyclotomic
public import ReasLib.FieldTheory.Finite.ProfiniteGalois

@[expose] public section
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualFiniteFieldTransport
variable (k : Type u) [Field k] [Finite k]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Actual finite-field completed-ring transport, with continuity in BOTH
directions and mixed universes; no arbitrary group-isomorphism transport. -/
def ringEquiv : completedGroupRing Λ Gal(AlgebraicClosure k/k) ≃+*
    completedGroupRing Λ (ProfiniteGrp.hatZ.{u} : Type u) :=
  completedGroupRing.ringEquiv Λ (FiniteField.ProfiniteGalois.galoisEquiv k)
    (FiniteField.ProfiniteGalois.galoisEquiv_continuous k)
    (FiniteField.ProfiniteGalois.galoisEquiv_inverse_continuous k)

def modules : ModuleCat.{u + 1} (completedGroupRing Λ Gal(AlgebraicClosure k/k)) ⥤
    ModuleCat.{u + 1} (completedGroupRing Λ (ProfiniteGrp.hatZ.{u} : Type u)) :=
  ModuleCat.restrictScalars (ringEquiv k Λ).symm.toRingHom

instance modules_additive : (modules k Λ).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (ringEquiv k Λ).symm.toRingHom).Additive)

/-- Transport a specified residual completed-module complex termwise. -/
def cochain (K : CochainComplex (ModuleCat.{u + 1}
    (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ) :=
  ((modules k Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

variable [HasDerivedCategory (ModuleCat.{u + 1}
    (completedGroupRing Λ (ProfiniteGrp.hatZ.{u} : Type u)))]

def derivedObject (K : CochainComplex (ModuleCat.{u + 1}
    (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ) :=
  DerivedCategory.Q.obj (cochain k Λ K)

end ActualFiniteFieldTransport
