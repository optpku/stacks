/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisRealization.Unit

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Schemes étale over a field are classified by discrete continuous actions of
the Galois group of any specified separable closure, with every orbit realized separately. -/
def galoisEquivalence (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] :
    Scheme.Etale (Spec (.of K)) ≌ DiscreteContAction TopCat.{u} Gal(Ksep/K) where
  functor := galoisFiber K Ksep
  inverse := GaloisRealization.functor K Ksep
  unitIso := GaloisRealization.unitIso K Ksep
  counitIso := GaloisRealization.counitIso K Ksep
  functor_unitIso_comp := sorry

/-- The equivalence retains the prescribed separable-closure-valued point functor. -/
theorem galoisEquivalence_functor (K Ksep : Type u) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    (galoisEquivalence K Ksep).functor = galoisFiber K Ksep := rfl

/-- The geometric-fiber functor identifies étale schemes over a field with discrete
continuous actions of the Galois group of a chosen separable closure. -/
instance galoisFiberIsEquivalence
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] :
    (galoisFiber K Ksep).IsEquivalence :=
  (galoisEquivalence K Ksep).isEquivalence_functor

end AlgebraicGeometry.Scheme.Etale

end
