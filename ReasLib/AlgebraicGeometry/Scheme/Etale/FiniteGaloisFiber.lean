/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisFiber
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Topology.Category.FinTopCat

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- An algebraically closed extension of a field determines a geometric point of its spectrum. -/
abbrev specFieldGeometricPoint (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar] :
    Scheme.GeometricPoint (Spec (.of K)) :=
  Scheme.GeometricPoint.of Kbar (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))

/-- The separable-closure-valued point fiber of a finite étale scheme over a field. -/
abbrev finiteEtaleSepFiber (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) : Type u :=
  (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
    (IsSepClosure.sep_closed K)
    (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj
      ((Scheme.FiniteEtale.toEtale (Spec (.of K))).obj Y)

/-- The separable-closure-valued point fiber of a finite étale scheme is finite. -/
instance finiteEtaleSepFiber_finite (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    Finite (finiteEtaleSepFiber K Ksep Y) := sorry

/-- Galois automorphisms act on separable-closure-valued points by precomposition. -/
instance finiteEtaleSepFiber_mulAction (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    MulAction Gal(Ksep/K) (finiteEtaleSepFiber K Ksep Y) where
  smul sigma element :=
    galoisPointAction K Ksep ((Scheme.FiniteEtale.toEtale (Spec (.of K))).obj Y)
      sigma element
  one_smul := sorry
  mul_smul := sorry

/-- The separable point fiber sends finite étale schemes to finite discrete continuous
Galois sets, with morphisms acting by postcomposition. -/
def finiteEtaleGaloisFiber (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    Scheme.FiniteEtale (Spec (.of K)) ⥤ DiscreteContAction FintypeCat.{u} Gal(Ksep/K) where
  obj Y :=
    ⟨⟨Action.FintypeCat.ofMulAction Gal(Ksep/K)
        (FintypeCat.of (finiteEtaleSepFiber K Ksep Y)), sorry⟩, sorry⟩
  map {Y Z} morphism :=
    ObjectProperty.homMk <| ObjectProperty.homMk
      { hom := FintypeCat.homMk
          ((@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
            (IsSepClosure.sep_closed K)
            (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.map
              ((Scheme.FiniteEtale.toEtale (Spec (.of K))).map morphism))
        comm := sorry }
  map_id := sorry
  map_comp := sorry

/-- The underlying finite set of the Galois fiber is the separable point fiber. -/
theorem finiteEtaleGaloisFiber_obj (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    ((finiteEtaleGaloisFiber K Ksep).obj Y).obj.obj.V =
      FintypeCat.of (finiteEtaleSepFiber K Ksep Y) :=
  rfl

/-- A finite étale morphism acts on separable point fibers by postcomposition. -/
theorem finiteEtaleGaloisFiber_map_apply (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    {Y Z : Scheme.FiniteEtale (Spec (.of K))}
    (morphism : Y ⟶ Z) (element : finiteEtaleSepFiber K Ksep Y) :
    ((finiteEtaleGaloisFiber K Ksep).map morphism).hom.hom.hom element =
      (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
        (IsSepClosure.sep_closed K)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.map
          ((Scheme.FiniteEtale.toEtale (Spec (.of K))).map morphism) element := sorry

/-- Scalar extension from a separable closure to an algebraically closed extension
sends separable points to geometric-fiber points. -/
def finiteEtaleSepFiber_toGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : finiteEtaleSepFiber K Ksep Y) :
    ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap Ksep Kbar)) ≫ element.left)
    (w := sorry)

/-- Scalar extension identifies the separable point fiber with the geometric fiber. -/
def finiteEtaleSepFiber_equivGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    finiteEtaleSepFiber K Ksep Y ≃ ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y :=
  Equiv.ofBijective (finiteEtaleSepFiber_toGeometric K Kbar Ksep Y) sorry

/-- Forgetting the finite Galois action gives the geometric-fiber functor by scalar extension. -/
def finiteEtaleGaloisFiber_comp_forget_iso (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    finiteEtaleGaloisFiber K Ksep ⋙
      (forget₂ (DiscreteContAction FintypeCat Gal(Ksep/K)) (ContAction FintypeCat Gal(Ksep/K)) ⋙
        forget₂ (ContAction FintypeCat Gal(Ksep/K)) FintypeCat) ≅
      (specFieldGeometricPoint K Kbar).finiteFiber :=
  NatIso.ofComponents
    (fun Y ↦
      { hom := FintypeCat.homMk (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y)
        inv := FintypeCat.homMk (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- Finite étale schemes over a field are equivalent to finite discrete continuous
actions of its separable Galois group. -/
instance finiteEtaleGaloisFiber_isEquivalence (K Ksep : Type u)
    [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    (finiteEtaleGaloisFiber K Ksep).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Etale

end
