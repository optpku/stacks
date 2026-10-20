/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Scalar
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kummer

open RingedSpace

variable {S : Scheme.{u}} {L N : S.Modules}

/-- Isomorphisms of modules with chosen tensor-power trivializations are precisely
the isomorphisms whose tensor-power maps commute with the trivializations. -/
noncomputable def isomorphisms (n : ℕ)
    (α : TensorPower.sheaf L n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (β : TensorPower.sheaf N n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules)) :
    Set (L ≅ N) :=
  {φ | TensorPower.map φ.hom n ≫ β.hom = α.hom}

/-- A global root of unity multiplies a module isomorphism through the scalar
automorphism of its target module. -/
noncomputable def rootOfUnityMul {n : ℕ} (ζ : rootsOfUnity n Γ(S, ⊤))
    (φ : L ≅ N) : L ≅ N :=
  φ ≪≫ unitScalarIso N ζ.val

/-- The set of isomorphisms compatible with tensor-power trivializations is empty
if no compatible isomorphism exists. -/
theorem isomorphisms_eq_empty (n : ℕ)
    (hL : Invertible L) (hN : Invertible N)
    (α : TensorPower.sheaf L n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (β : TensorPower.sheaf N n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (h_no_isomorphism : ¬ ∃ φ : L ≅ N, TensorPower.map φ.hom n ≫ β.hom = α.hom) :
    isomorphisms n α β = ∅ := sorry

/-- Compatible isomorphisms between invertible modules with tensor-power
trivializations form the global roots-of-unity orbit of any compatible isomorphism. -/
theorem isomorphisms_eq_rootOfUnity_orbit (n : ℕ)
    (hL : Invertible L) (hN : Invertible N)
    (α : TensorPower.sheaf L n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (β : TensorPower.sheaf N n ≅ (SheafOfModules.unit S.ringCatSheaf : S.Modules))
    (φ : L ≅ N) (hφ : TensorPower.map φ.hom n ≫ β.hom = α.hom) :
    isomorphisms n α β =
      Set.range (fun ζ : rootsOfUnity n Γ(S, ⊤) ↦ rootOfUnityMul ζ φ) := sorry

end AlgebraicGeometry.Scheme.Modules.Kummer
