/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.FiniteGaloisFiber
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Galois.Topology

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

private theorem continuous_aut_of_continuous_eval
    {C : Type*} [Category C] {G : Type*} [TopologicalSpace G]
    (F : C ⥤ FintypeCat.{u}) (f : G → Aut F)
    (h : ∀ (Y : C) (element : F.obj Y),
      Continuous (fun g ↦ (f g).hom.app Y element)) : Continuous f := by
  letI (Y : C) : TopologicalSpace (Aut (F.obj Y)) := ⊥
  letI (Y : C) : DiscreteTopology (Aut (F.obj Y)) := ⟨rfl⟩
  apply (PreGaloisCategory.autEmbedding_isClosedEmbedding F).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro Y
  let evaluation : Aut (F.obj Y) → (F.obj Y → F.obj Y) := fun a ↦ a.hom
  have hinj : Function.Injective evaluation := by
    intro a b hab
    apply Iso.ext
    ext element
    exact congr_fun hab element
  have hemb :=
    (continuous_of_discreteTopology : Continuous evaluation).isClosedEmbedding hinj
  apply hemb.isEmbedding.continuous_iff.mpr
  exact continuous_pi (h Y)

/-- The Galois action on separable point fibers induces a continuous homomorphism
to the automorphism group of the geometric-fiber functor. -/
def galoisToFundamentalGroup (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    ContinuousMonoidHom Gal(Ksep/K) (Aut ((specFieldGeometricPoint K Kbar).finiteFiber)) where
  toFun sigma :=
    (finiteEtaleGaloisFiber_comp_forget_iso K Kbar Ksep).conjAut
      (NatIso.ofComponents
        (fun Y ↦
          { hom := FintypeCat.homMk
              (fun element : finiteEtaleSepFiber K Ksep Y ↦ sigma • element)
            inv := FintypeCat.homMk
              (fun element : finiteEtaleSepFiber K Ksep Y ↦ sigma⁻¹ • element)
            hom_inv_id := by
              ext element
              exact inv_smul_smul sigma (show finiteEtaleSepFiber K Ksep Y from element)
            inv_hom_id := by
              ext element
              exact smul_inv_smul sigma (show finiteEtaleSepFiber K Ksep Y from element) })
        (fun {Y Z} morphism ↦ by
          ext element
          exact (ConcreteCategory.congr_hom
            (((finiteEtaleGaloisFiber K Ksep).map morphism).hom.hom.comm sigma)
            element).symm))
  map_one' := by
    calc
      _ = (finiteEtaleGaloisFiber_comp_forget_iso K Kbar Ksep).conjAut 1 := by
        congr 1
        ext Y element
        exact one_smul Gal(Ksep/K) (show finiteEtaleSepFiber K Ksep Y from element)
      _ = 1 := map_one _
  map_mul' sigma tau := by
    rw [← map_mul]
    congr 1
    ext Y element
    exact mul_smul sigma tau (show finiteEtaleSepFiber K Ksep Y from element)
  continuous_toFun := by
    apply continuous_aut_of_continuous_eval (specFieldGeometricPoint K Kbar).finiteFiber
    intro Y element
    letI : TopologicalSpace (finiteEtaleSepFiber K Ksep Y) := ⊥
    letI : DiscreteTopology (finiteEtaleSepFiber K Ksep Y) := ⟨rfl⟩
    have hsmul : Continuous (fun p : Gal(Ksep/K) × finiteEtaleSepFiber K Ksep Y ↦
        p.1 • p.2) :=
      ((finiteEtaleGaloisFiber K Ksep).obj Y).obj.property.continuous_smul
    simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app, FintypeCat.comp_apply]
    change Continuous (fun sigma : Gal(Ksep/K) ↦
      (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y)
        (sigma • (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm element))
    have he : Continuous (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y :
        finiteEtaleSepFiber K Ksep Y → ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :=
      continuous_of_discreteTopology
    have hp : Continuous (fun sigma : Gal(Ksep/K) ↦
        (sigma, (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm element)) :=
      continuous_id.prodMk continuous_const
    have hs := hsmul.comp hp
    have hc := he.comp hs
    exact hc

/-- The Galois comparison acts on geometric fibers by conjugating the separable-fiber
action along scalar extension. -/
theorem galoisToFundamentalGroup_apply (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep]
    (sigma : Gal(Ksep/K)) (Y : Scheme.FiniteEtale (Spec (.of K)))
    (element : ((specFieldGeometricPoint K Kbar).finiteFiber).obj Y) :
    ((galoisToFundamentalGroup K Kbar Ksep sigma).hom.app Y) element =
      (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y)
        (sigma • (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm element) :=
  rfl

/-- The canonical Galois comparison is an isomorphism of profinite topological groups. -/
theorem galoisToFundamentalGroup_isHomeomorph (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    IsHomeomorph (galoisToFundamentalGroup K Kbar Ksep) := sorry

end AlgebraicGeometry.Scheme.Etale

end
