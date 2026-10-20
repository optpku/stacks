/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Isomorphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

/- 59.28.4.1 (1): the isomorphism set of invertible modules with tensor-power
trivializations is empty when no compatible isomorphism exists. -/
@[stacks 040P] #check
  (AlgebraicGeometry.Scheme.Modules.Kummer.isomorphisms_eq_empty :
    ∀ {S : Scheme.{u}} {L N : S.Modules} (n : ℕ)
      (hL : Scheme.Modules.Invertible L) (hN : Scheme.Modules.Invertible N)
      (α : TensorPower.sheaf L n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
      (β : TensorPower.sheaf N n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules)),
      (¬ ∃ φ : L ≅ N, TensorPower.map φ.hom n ≫ β.hom = α.hom) →
        Scheme.Modules.Kummer.isomorphisms n α β = ∅)

/- 59.28.4.1 (2): compatible isomorphisms between invertible modules with
tensor-power trivializations form the global roots-of-unity orbit of any one of them. -/
@[stacks 040P] #check
  (AlgebraicGeometry.Scheme.Modules.Kummer.isomorphisms_eq_rootOfUnity_orbit :
    ∀ {S : Scheme.{u}} {L N : S.Modules} (n : ℕ),
      Scheme.Modules.Invertible L → Scheme.Modules.Invertible N →
      ∀ (α : TensorPower.sheaf L n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
        (β : TensorPower.sheaf N n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
        (φ : L ≅ N),
        TensorPower.map φ.hom n ≫ β.hom = α.hom →
          Scheme.Modules.Kummer.isomorphisms n α β =
            Set.range (fun ζ : rootsOfUnity n Γ(S, ⊤) ↦
              Scheme.Modules.Kummer.rootOfUnityMul ζ φ))
