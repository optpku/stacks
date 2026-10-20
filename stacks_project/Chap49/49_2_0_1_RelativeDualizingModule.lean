/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/- The dual module action has the expected `B`-linear dual carrier. -/
#check (Algebra.DualModule.module :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    Module B (Module.Dual A B))

/- The `A`-linear dual is packaged as a `B`-module object. -/
#check (Algebra.DualModule.of :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ModuleCat B)

/- The dual module action computes by precomposition with multiplication. -/
#check (Algebra.DualModule.smul_apply :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b x : B) (f : Algebra.DualModule.of A B),
    (b • f : Module.Dual A B) x = (f : Module.Dual A B) (b * x))

/- The relative dualizing module is the scalar extension of the dual module. -/
#check (Algebra.RelativeDualizingModule.of :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (_h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (_h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
    ModuleCat B)

/- The defining equality identifies the relative dualizing module with the tensor product. -/
#check (Algebra.RelativeDualizingModule.of_eq :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
    Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open =
      @ModuleCat.of B _ (Algebra.DualModule.of A B' ⊗[B'] B) _ TensorProduct.Right.module)
