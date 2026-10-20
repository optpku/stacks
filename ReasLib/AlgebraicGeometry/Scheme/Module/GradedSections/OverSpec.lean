/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Section rings over an affine base

This file packages the algebra structure on a tensor-power section ring induced by a scheme
morphism to an affine base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The base-ring map into the section ring induced by a morphism to the affine base. -/
@[stacks 0B5T "affine-base map into a tensor-power section ring"]
noncomputable def sectionRingAlgMap
    (f : X ⟶ Spec (CommRingCat.of R))
    (L : X.Modules) [L.Invertible] :
    R →+* RingedSpace.GradedSections.ring (X := X.toRingedSpace) L :=
  (algebraMap (RingedSpace.globalSectionsRing X.toRingedSpace)
    (RingedSpace.GradedSections.ring (X := X.toRingedSpace) L)).comp (globalSectionsMap f)

/-- The tensor-power section ring, bundled with the algebra structure induced by a morphism to
an affine base. -/
@[stacks 0B5T "tensor-power section-ring algebra over an affine base"]
noncomputable def sectionRingAlg
    (f : X ⟶ Spec (CommRingCat.of R))
    (L : X.Modules) [L.Invertible] : CommAlgCat R :=
  @CommAlgCat.of R _ (RingedSpace.GradedSections.ring (X := X.toRingedSpace) L) _
    (sectionRingAlgMap f L).toAlgebra

end AlgebraicGeometry.Scheme.Hom
