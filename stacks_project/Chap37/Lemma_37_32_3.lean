/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.LinearSystem.Bertini
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

/- Lemma 37.32.3: if a finite-type geometrically irreducible scheme has three members of a
linear system whose second and third meet in a codimension-two component not contained in the
first, and every component of the base locus has codimension at least two, then a general member
of the linear system is geometrically irreducible. -/
@[stacks 0G4F] #check (AlgebraicGeometry.LinearSystem.holdsForGeneralVector_geometricallyIrreducible :
    {k : Type} → [Field k] → {V : Type} → [AddCommGroup V] → [Module k V] → {r : ℕ} →
    (X : Over (Spec (CommRingCat.of k))) → [Scheme.Hom.FiniteType X.hom] →
    [GeometricallyIrreducible X.hom] →
    (ℒ : X.left.Modules) → [Scheme.Modules.Invertible ℒ] →
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ) →
    (b : Module.Basis (Fin r) k V) →
    let H : V → Closeds X.left := fun v ↦
      (Scheme.zeroIdealSheaf ℒ (RingedSpace.sectionFromTop ℒ (ψ v))).support
    ∀ (h_component : ∃ v₁ v₂ v₃ : V, ∃ Z : IrreducibleCloseds X.left,
        Maximal (fun Y : IrreducibleCloseds X.left ↦
          (Y : Set X.left) ⊆ (H v₂ : Set X.left) ∩ (H v₃ : Set X.left)) Z ∧
          ¬(Z : Set X.left) ⊆ (H v₁ : Set X.left) ∧
          Order.coheight Z = (2 : ℕ∞))
      (h_baseLocus : Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast
        2 (⋂ v : V, (H v : Set X.left))),
      AlgebraicGeometry.LinearSystem.HoldsForGeneralVector b (fun K _ _ v ↦
        GeometricallyIrreducible
          (AlgebraicGeometry.LinearSystem.fiberDivisorToSpecOfHom X K ℒ ψ b v)))
