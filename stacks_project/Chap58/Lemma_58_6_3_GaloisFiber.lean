module

public import stacks_project.Chap58.Lemma_58_2_2_GaloisFiber
public import stacks_project.Chap58.Lemma_58_3_3_Fiber
public import stacks_project.Chap58.Lemma_58_3_1
public import stacks_project.Chap58.Lemma_58_5_5
public import stacks_project.Chap58.Lemma_58_5_5_Fiber
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Galois
public import ReasLib.AlgebraicGeometry.Scheme.Etale.FiniteGaloisEquivalence

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open scoped FintypeCatDiscrete

universe u

variable (K Kbar Ksep : Type u)
variable [Field K] [Field Kbar] [Field Ksep]
variable [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
variable [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
variable (Y Z : Scheme.FiniteEtale (Spec (.of K)))
variable (morphism : Y ⟶ Z) (element : finiteEtaleSepFiber K Ksep Y)

#check (AlgebraicGeometry.Scheme.Etale.specFieldGeometricPoint K Kbar :
  Scheme.GeometricPoint (Spec (.of K)))
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleSepFiber K Ksep Y : Type u)
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleSepFiber_finite K Ksep Y :
  Finite (finiteEtaleSepFiber K Ksep Y))
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleSepFiber_mulAction K Ksep Y :
  MulAction Gal(Ksep/K) (finiteEtaleSepFiber K Ksep Y))
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber K Ksep :
  Scheme.FiniteEtale (Spec (.of K)) ⥤ DiscreteContAction FintypeCat.{u} Gal(Ksep/K))
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber_obj K Ksep Y :
  ((finiteEtaleGaloisFiber K Ksep).obj Y).obj.obj.V =
    FintypeCat.of (finiteEtaleSepFiber K Ksep Y))
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber_map_apply K Ksep morphism element :
  ((finiteEtaleGaloisFiber K Ksep).map morphism).hom.hom.hom element =
    (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
      (IsSepClosure.sep_closed K)
      (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.map
        ((Scheme.FiniteEtale.toEtale (Spec (.of K))).map morphism) element)
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleSepFiber_toGeometric K Kbar Ksep Y :
  finiteEtaleSepFiber K Ksep Y → ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y)
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y :
  finiteEtaleSepFiber K Ksep Y ≃ ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y)
#check (AlgebraicGeometry.Scheme.Etale.finiteEtaleGaloisFiber_comp_forget_iso K Kbar Ksep :
  finiteEtaleGaloisFiber K Ksep ⋙
    (forget₂ (DiscreteContAction FintypeCat Gal(Ksep/K)) (ContAction FintypeCat Gal(Ksep/K)) ⋙
      forget₂ (ContAction FintypeCat Gal(Ksep/K)) FintypeCat) ≅
    (specFieldGeometricPoint K Kbar).finiteFiber)
#check (AlgebraicGeometry.Scheme.Etale.galoisToFundamentalGroup K Kbar Ksep :
  ContinuousMonoidHom Gal(Ksep/K) (Aut ((specFieldGeometricPoint K Kbar).finiteFiber)))
#check (AlgebraicGeometry.Scheme.Etale.galoisToFundamentalGroup_apply K Kbar Ksep :
  ∀ (sigma : Gal(Ksep/K)) (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y),
    ((galoisToFundamentalGroup K Kbar Ksep sigma).hom.app Y) element =
      (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y)
        (sigma • (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm element))
