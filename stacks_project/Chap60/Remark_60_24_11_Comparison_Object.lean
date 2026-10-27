/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.DividedPowers
public import stacks_project.Chap60.Proposition_60_21_1

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace AlgebraicGeometry.Scheme.Crystalline
variable {A : Type u} [CommRing A]
/-- The affine-open specialization of the section map induced by a morphism to Spec A. -/
noncomputable abbrev affineSectionMap {T : Scheme.{u}} (g : T ⟶ Spec (.of A))
    (V : T.affineOpens) : A →+* Γ(T, V) :=
  Scheme.Hom.sectionsMap g V

export DividedPowers (extensionAlong extensionAlong_spec dividedPowers_ofIdealEq)
end AlgebraicGeometry.Scheme.Crystalline
