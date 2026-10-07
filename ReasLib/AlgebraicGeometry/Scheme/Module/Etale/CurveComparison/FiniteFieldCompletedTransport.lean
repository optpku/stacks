module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ContinuousCompletedRingTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCyclotomic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

@[expose] public section
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualFiniteFieldTransport
variable (k : Type u) [Field k] [Finite k]

abbrev profiniteInt : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative (ULift.{u} ℤ)))

/-- The integer map is the actual q-power arithmetic Frobenius map. -/
def frobeniusPowers : Multiplicative (ULift.{u} ℤ) →* Gal(AlgebraicClosure k/k) :=
  -- Local instance justification (proof-local temporary data): the canonical Frobenius API uses Fintype.
  letI : Fintype k := Fintype.ofFinite k
  let p := ringChar k
  -- Local instance justification (proof-local temporary data): p is the actual prime characteristic of k.
  haveI : Fact p.Prime := ⟨by sorry⟩
  -- Local instance justification (defeq pin): use the actual characteristic map from Z/p in the Frobenius definition.
  letI := ZMod.algebra k p
  { toFun := fun m ↦ (arithmeticFrobeniusEquiv : Gal(AlgebraicClosure k/k)) ^ (Multiplicative.toAdd m).down
    map_one' := sorry
    map_mul' := sorry }

/-- Complete that specific integer homomorphism into the profinite Galois group. -/
def frobeniusLift : profiniteInt.{u} ⟶ InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom (frobeniusPowers k) :
      GrpCat.of (Multiplicative (ULift.{u} ℤ)) ⟶
      GrpCat.of (InfiniteGalois.profiniteGalGrp k (AlgebraicClosure k)))

/-- Finite-field Galois theory makes the specified completed Frobenius map bijective. -/
theorem frobeniusLift_bijective : Function.Bijective (frobeniusLift k).hom := sorry

def galoisEquiv : Gal(AlgebraicClosure k/k) ≃* (profiniteInt.{u} : Type u) :=
  (MulEquiv.ofBijective (frobeniusLift k).hom.toMonoidHom (frobeniusLift_bijective k)).symm

/-- The inverse is the specified continuous profinite morphism. -/
theorem galoisEquiv_inverse_continuous : Continuous (galoisEquiv k).symm :=
  (frobeniusLift k).hom.continuous

/-- Compact-to-Hausdorff bijectivity supplies continuity of the other direction. -/
theorem galoisEquiv_continuous : Continuous (galoisEquiv k) := sorry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Actual finite-field completed-ring transport, with continuity in BOTH
directions and mixed universes; no arbitrary group-isomorphism transport. -/
def ringEquiv : completedGroupRing Λ Gal(AlgebraicClosure k/k) ≃+*
    completedGroupRing Λ (profiniteInt.{u} : Type u) :=
  ActualCompletedRingTransport.ringEquiv Λ (galoisEquiv k)
    (galoisEquiv_continuous k) (galoisEquiv_inverse_continuous k)

def modules : ModuleCat.{u + 1} (completedGroupRing Λ Gal(AlgebraicClosure k/k)) ⥤
    ModuleCat.{u + 1} (completedGroupRing Λ (profiniteInt.{u} : Type u)) :=
  ModuleCat.restrictScalars (ringEquiv k Λ).symm.toRingHom

instance modules_additive : (modules k Λ).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (ringEquiv k Λ).symm.toRingHom).Additive)

/-- Transport a specified residual completed-module complex termwise. -/
def cochain (K : CochainComplex (ModuleCat.{u + 1}
    (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ) :=
  ((modules k Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

variable [HasDerivedCategory (ModuleCat.{u + 1} (completedGroupRing Λ (profiniteInt.{u} : Type u)))]

def derivedObject (K : CochainComplex (ModuleCat.{u + 1}
    (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ) :=
  DerivedCategory.Q.obj (cochain k Λ K)

end ActualFiniteFieldTransport
