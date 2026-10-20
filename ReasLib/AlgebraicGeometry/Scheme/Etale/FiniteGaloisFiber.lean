/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisFiber
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import Mathlib.AlgebraicGeometry.AffineScheme
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

/-- The specified embedding lands in the relative separable closure inside `Kbar`. -/
def finiteEtaleSepFiber_separableInclusion (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    Ksep →ₐ[K] separableClosure K Kbar :=
  (IsScalarTower.toAlgHom K Ksep Kbar).codRestrict (separableClosure K Kbar).toSubalgebra
    (fun x ↦ (Algebra.IsSeparable.isSeparable K x).map _
      (RingHom.injective (algebraMap Ksep Kbar)))

/-- The given separable closure is the relative separable closure inside `Kbar`. -/
def finiteEtaleSepFiber_separableEquiv (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    Ksep ≃ₐ[K] separableClosure K Kbar := by
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  exact AlgEquiv.ofBijective (finiteEtaleSepFiber_separableInclusion K Kbar Ksep)
    (Algebra.IsAlgebraic.algHom_bijective₂
      (finiteEtaleSepFiber_separableInclusion K Kbar Ksep)
      (IsSepClosed.lift : separableClosure K Kbar →ₐ[K] Ksep)).1

/-- A geometric fiber point evaluates global functions of its finite étale scheme. -/
def finiteEtaleSepFiber_geometricEvaluation (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    Γ(Y.left, ⊤) →+* Kbar :=
  (element.left.appTop ≫ (Scheme.ΓSpecIso (.of Kbar)).hom).hom

/-- Finite étaleness makes every value of a geometric point separable over the base field. -/
theorem finiteEtaleSepFiber_geometricEvaluation_isSeparable (K Kbar : Type u)
    [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) (r : Γ(Y.left, ⊤)) :
    IsSeparable K (finiteEtaleSepFiber_geometricEvaluation K Kbar Y element r) := sorry

/-- Evaluate a geometric fiber point in the given separable closure, by restricting its
actual values to the relative separable closure and applying the specified field inverse. -/
def finiteEtaleSepFiber_separableEvaluation (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    Γ(Y.left, ⊤) →+* Ksep :=
  (finiteEtaleSepFiber_separableEquiv K Kbar Ksep).symm.toRingHom.comp
    ((finiteEtaleSepFiber_geometricEvaluation K Kbar Y element).codRestrict
      (separableClosure K Kbar).toSubalgebra.toSubsemiring
      (finiteEtaleSepFiber_geometricEvaluation_isSeparable K Kbar Y element))

/-- A geometric fiber point descends to the given separable closure through the actual
affine presentation of the finite étale scheme. -/
def finiteEtaleSepFiber_fromGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    finiteEtaleSepFiber K Ksep Y := by
  let hfinite : AlgebraicGeometry.IsFinite Y.hom := Y.prop.1
  let haffine : IsAffineHom Y.hom := hfinite.toIsAffineHom
  let hbase : IsAffine ((Functor.fromPUnit (Spec (.of K))).obj Y.right) := by
    change IsAffine (Spec (.of K))
    infer_instance
  letI : IsAffine Y.left := @isAffine_of_isAffineHom _ _ Y.hom haffine hbase
  exact Over.homMk
    (Spec.map (CommRingCat.ofHom
      (finiteEtaleSepFiber_separableEvaluation K Kbar Ksep Y element)) ≫ Y.left.isoSpec.inv)
    (w := sorry)

/-- Descent to the separable closure followed by scalar extension is the original point. -/
theorem finiteEtaleSepFiber_toGeometric_fromGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    finiteEtaleSepFiber_toGeometric K Kbar Ksep Y
      (finiteEtaleSepFiber_fromGeometric K Kbar Ksep Y element) = element := sorry

/-- Scalar extension followed by descent preserves every separable-closure-valued point. -/
theorem finiteEtaleSepFiber_fromGeometric_toGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) (element : finiteEtaleSepFiber K Ksep Y) :
    finiteEtaleSepFiber_fromGeometric K Kbar Ksep Y
      (finiteEtaleSepFiber_toGeometric K Kbar Ksep Y element) = element := sorry

/-- Scalar extension identifies the separable point fiber with the geometric fiber. -/
def finiteEtaleSepFiber_equivGeometric (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (Y : Scheme.FiniteEtale (Spec (.of K))) :
    finiteEtaleSepFiber K Ksep Y ≃ ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y where
  toFun := finiteEtaleSepFiber_toGeometric K Kbar Ksep Y
  invFun := finiteEtaleSepFiber_fromGeometric K Kbar Ksep Y
  left_inv := finiteEtaleSepFiber_fromGeometric_toGeometric K Kbar Ksep Y
  right_inv := finiteEtaleSepFiber_toGeometric_fromGeometric K Kbar Ksep Y

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

end AlgebraicGeometry.Scheme.Etale

end
