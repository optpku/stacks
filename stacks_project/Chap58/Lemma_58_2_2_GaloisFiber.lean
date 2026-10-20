/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisEquivalence

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

#check (TopCat.hasForget₂Self : HasForget₂ TopCat TopCat)
#check (AlgebraicGeometry.Scheme.Etale.galoisPointAction :
  ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep],
    (X : Scheme.Etale (Spec (.of K))) → (σ : Gal(Ksep/K)) →
      (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
        (IsSepClosure.sep_closed K)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X →
      (@Scheme.pointSmallEtale (Spec (.of K)) Ksep inferInstance
        (IsSepClosure.sep_closed K)
        (Spec.map (CommRingCat.ofHom (algebraMap K Ksep)))).fiber.obj X)
#check (AlgebraicGeometry.Scheme.Etale.galoisFiber :
  ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep],
    Scheme.Etale (Spec (.of K)) ⥤ DiscreteContAction TopCat Gal(Ksep/K))
#check AlgebraicGeometry.Scheme.Etale.galoisFiber_obj_carrier
#check AlgebraicGeometry.Scheme.Etale.galoisFiber_smul_apply
#check AlgebraicGeometry.Scheme.Etale.galoisFiber_map_apply
#check (AlgebraicGeometry.Scheme.Etale.galoisFiberIsEquivalence :
  ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep],
    (AlgebraicGeometry.Scheme.Etale.galoisFiber K Ksep).IsEquivalence)

#check AlgebraicGeometry.Scheme.Etale.galoisEquivalence_functor
