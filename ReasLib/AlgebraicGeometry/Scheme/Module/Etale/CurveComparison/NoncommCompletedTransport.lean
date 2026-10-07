module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedRing
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

/-- Pull back actual open normal subgroups through the continuous group map. -/
def comap (N : OpenNormalSubgroup H) : OpenNormalSubgroup G :=
  ⟨N.toOpenSubgroup.comap e.toMonoidHom he,
    show (N.toSubgroup.comap e.toMonoidHom).Normal from N.isNormal'.comap e.toMonoidHom⟩

/-- The actual finite group-algebra stage map over a NONCOMMUTATIVE ring. -/
def stage (N : OpenNormalSubgroup H) :
    MonoidAlgebra R (G ⧸ (comap e he N).toSubgroup) →+* MonoidAlgebra R (H ⧸ N.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom R
    (QuotientGroup.map (comap e he N).toSubgroup N.toSubgroup e.toMonoidHom
      (by intro x hx; exact hx))

/-- The actual compatible-family ring map. -/
def hom : NoncommCompletedRing.Obj R G →+* NoncommCompletedRing.Obj R H where
  toFun x := ⟨fun N ↦ stage R e he N (x.val (comap e he N)), by sorry⟩
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Both continuous directions are required, including for mixed group universes. -/
def ringEquiv : NoncommCompletedRing.Obj R G ≃+* NoncommCompletedRing.Obj R H where
  toFun := hom R e he
  invFun := hom R e.symm heinv
  left_inv := by sorry
  right_inv := by sorry
  map_add' := (hom R e he).map_add
  map_mul' := (hom R e he).map_mul

/-- Actual completed scalar restriction, preserving carriers and coefficient maps. -/
def modules : ModuleCat.{m} (NoncommCompletedRing.Obj R G) ⥤
    ModuleCat.{m} (NoncommCompletedRing.Obj R H) :=
  ModuleCat.restrictScalars (ringEquiv R e he heinv).symm.toRingHom

instance modules_additive : (modules R e he heinv).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (ringEquiv R e he heinv).symm.toRingHom).Additive)

section Coefficients
variable {S : Type r} [Ring S]

/-- A coefficient homomorphism acts on every finite-stage coefficient,
without commuting it with any coefficient of R. -/
def coefficientHom (f : R →+* S) :
    NoncommCompletedRing.Obj R G →+* NoncommCompletedRing.Obj S G where
  toFun x := ⟨fun N ↦ MonoidAlgebra.mapRingHom (G ⧸ N.toSubgroup) f (x.val N), by sorry⟩
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Coefficient transport uses the specified ring equivalence on each quotient. -/
def coefficientEquiv (f : R ≃+* S) :
    NoncommCompletedRing.Obj R G ≃+* NoncommCompletedRing.Obj S G where
  toFun := coefficientHom R f.toRingHom
  invFun := coefficientHom S f.symm.toRingHom
  left_inv := by sorry
  right_inv := by sorry
  map_add' := (coefficientHom R f.toRingHom).map_add
  map_mul' := (coefficientHom R f.toRingHom).map_mul

end Coefficients

/-- Canonical removal of double-opposite coefficients, retaining the residual group. -/
def doubleOppositeModules : ModuleCat.{m} (NoncommCompletedRing.Obj Rᵐᵒᵖᵐᵒᵖ G) ⥤
    ModuleCat.{m} (NoncommCompletedRing.Obj R G) :=
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
def modules : ModuleCat.{u + 1} (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)) ⥤
    ModuleCat.{u + 1} (NoncommCompletedRing.Obj R
      (ActualFiniteFieldTransport.profiniteInt.{u} : Type u)) :=
  NoncommCompletedTransport.modules R (ActualFiniteFieldTransport.galoisEquiv k)
    (ActualFiniteFieldTransport.galoisEquiv_continuous k)
    (ActualFiniteFieldTransport.galoisEquiv_inverse_continuous k)

end NoncommFiniteFieldTransport
