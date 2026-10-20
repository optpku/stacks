module

public import ReasLib.RepresentationTheory.CompletedGroupRing.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteFieldCompletedTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

@[expose] public section
open CategoryTheory
noncomputable section
universe r v w m

namespace NoncommCompletedTransport
variable (R : Type r) [Ring R]
variable {G : Type v} {H : Type w}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (e : G ≃* H) (he : Continuous e) (heinv : Continuous e.symm)

section Coefficients
variable {S : Type r} [Ring S]

/-- A coefficient homomorphism acts on every finite-stage coefficient,
without commuting it with any coefficient of R. -/
def coefficientHom (f : R →+* S) :
    completedGroupRing R G →+* completedGroupRing S G where
  toFun x := ⟨fun N ↦ MonoidAlgebra.mapRingHom (G ⧸ N.toSubgroup) f (x.val N), by sorry⟩
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Coefficient transport uses the specified ring equivalence on each quotient. -/
def coefficientEquiv (f : R ≃+* S) :
    completedGroupRing R G ≃+* completedGroupRing S G where
  toFun := coefficientHom R f.toRingHom
  invFun := coefficientHom S f.symm.toRingHom
  left_inv := by sorry
  right_inv := by sorry
  map_add' := (coefficientHom R f.toRingHom).map_add
  map_mul' := (coefficientHom R f.toRingHom).map_mul

end Coefficients

/-- Canonical removal of double-opposite coefficients, retaining the residual group. -/
def doubleOppositeModules : ModuleCat.{m} (completedGroupRing Rᵐᵒᵖᵐᵒᵖ G) ⥤
    ModuleCat.{m} (completedGroupRing R G) :=
  ModuleCat.restrictScalars (coefficientHom R (G := G) (RingEquiv.opOp R).toRingHom)

instance doubleOppositeModules_additive : (doubleOppositeModules R (G := G)).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars
    (coefficientHom R (G := G) (RingEquiv.opOp R).toRingHom)).Additive)

end NoncommCompletedTransport

namespace NoncommFiniteFieldTransport
universe u
variable (k : Type u) [Field k] [Finite k]
variable (R : Type (u + 1)) [Ring R]

/-- The separately authorized finite-field specialization uses the same actual
arithmetic Frobenius, now with arbitrary coefficient ring R. -/
def modules : ModuleCat.{u + 1} (completedGroupRing R Gal(AlgebraicClosure k/k)) ⥤
    ModuleCat.{u + 1} (completedGroupRing R
      (ProfiniteGrp.hatZ.{u} : Type u)) :=
  completedGroupRing.restrictScalars R (FiniteField.ProfiniteGalois.galoisEquiv k)
    (FiniteField.ProfiniteGalois.galoisEquiv_continuous k)
    (FiniteField.ProfiniteGalois.galoisEquiv_inverse_continuous k)

end NoncommFiniteFieldTransport
