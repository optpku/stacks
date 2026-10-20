/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derivation.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open SheafOfModules
open PresheafOfModules.Derivation'

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- A relative derivation of the structure sheaf fixes a closed point when its induced stalk
derivation preserves the maximal ideal of the local ring at that point. -/
def derivationFixesAt
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (x : closedPoints X.left) : Prop :=
  let Y := X.left
  let A := stalkRing X x
  let δ := stalk D x
  let ι := unitStalkToRingStalk Y.sheaf x
  ∀ s : A, s ∈ IsLocalRing.maximalIdeal A →
    ι (δ.d s) ∈ IsLocalRing.maximalIdeal A

/-- A structure-sheaf derivation is zero when all of its sectionwise additive maps vanish. -/
def derivationIsZero
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) : Prop :=
  let Y := X.left
  let F := Y.presheaf
  ∀ U : (Opens Y)ᵒᵖ, ∀ s : F.obj U, D.d s = 0

/-- Every derivation of the structure sheaf is zero on a smooth proper curve whose genus is at
least two. -/
theorem derivation_eq_zero_of_two_le_genus
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) :
    derivationIsZero X D := sorry

/-- A nonzero derivation of the structure sheaf fixes no closed point on a smooth proper curve
whose genus is one. -/
theorem not_derivationFixesAt_of_genus_eq_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 1)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (hD : ¬ derivationIsZero X D) (x : closedPoints X.left) :
    ¬ derivationFixesAt X D x := sorry

/-- A nonzero derivation of the structure sheaf fixes at most two closed points on a smooth proper
curve whose genus is zero. -/
theorem encard_derivationFixesAt_le_two_of_genus_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (hD : ¬ derivationIsZero X D) :
    Set.encard {x : closedPoints X.left | derivationFixesAt X D x} ≤ 2 := sorry

end AlgebraicGeometry.Curve
