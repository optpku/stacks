/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule Algebra.Product TensorProduct TensorProduct.Right

universe u

/- Definition 49.4.1: for a flat quasi-finite map of Noetherian rings, a trace element
of `ω_{B/A}` is characterized by mapping to the finite trace after every Noetherian base
change and product decomposition with finite first factor. -/
@[stacks 0BT6] #check (Algebra.RelativeDualizingModule.TraceElement.IsUniversal :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B] (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
      (τ : Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open),
      Prop)
