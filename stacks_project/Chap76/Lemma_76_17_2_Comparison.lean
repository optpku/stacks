/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

/-!
# Compatibility for canonical relative derivations

The compatibility conversion preserves the underlying derivation and its certificates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- The canonical derivation, with its additive map and relative-base certificate
unchanged. -/
def ofCanonicalDerivation {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : Hom.derivations f F) : Hom.derivations f F where
  d := D.d
  d_mul := by intro U a b; exact D.d_mul a b
  d_map := by intro U V g a; exact D.d_map g a
  d_app := by intro U a; exact D.d_app a

/-- Converting the relative-base certificate leaves every value of the derivation unchanged. -/
theorem ofCanonicalDerivation_apply {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : Hom.derivations f F) (U : (smallEtaleSite X)ᵒᵖ)
    (a : (commStructureSheaf X).obj.obj U) :
    (ofCanonicalDerivation f F D).d a = D.d a := rfl

/-- The comparison loses no derivation data. -/
theorem ofCanonicalDerivation_injective {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) : Function.Injective (ofCanonicalDerivation f F) := by
  intro D E h
  ext U a
  exact congrArg (fun q ↦ q.d (X := U) a) h
end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
