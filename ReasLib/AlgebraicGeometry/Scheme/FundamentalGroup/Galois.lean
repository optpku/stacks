/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
            hom_inv_id := sorry
            inv_hom_id := sorry })
        (fun _ ↦ sorry))
  map_one' := sorry
  map_mul' := sorry
  continuous_toFun := sorry

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
        (sigma • (finiteEtaleSepFiber_equivGeometric K Kbar Ksep Y).symm element) := sorry

/-- The canonical Galois comparison is an isomorphism of profinite topological groups. -/
theorem galoisToFundamentalGroup_isHomeomorph (K Kbar Ksep : Type u)
    [Field K] [Field Kbar] [Field Ksep]
    [Algebra K Kbar] [Algebra K Ksep] [Algebra Ksep Kbar]
    [IsScalarTower K Ksep Kbar] [IsAlgClosed Kbar] [IsSepClosure K Ksep] :
    IsHomeomorph (galoisToFundamentalGroup K Kbar Ksep) := sorry

end AlgebraicGeometry.Scheme.Etale

end
