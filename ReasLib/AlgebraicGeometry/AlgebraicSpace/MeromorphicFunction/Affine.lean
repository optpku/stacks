/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-!
# Regular sections on affine étale charts

On an affine scheme étale over an algebraic space, regular structure sections
are precisely the nonzerodivisors of its ring of sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an affine étale chart of an algebraic space, the regular-section submonoid
equals the nonzerodivisors of its ring of structure sections. -/
theorem regularStructureSections_eq_nonZeroDivisors
    {S : Scheme.{u}} {X : AlgebraicSpace S} (U : affineEtaleSite X) :
    (regularStructureSections X).obj (op U.obj) =
      nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)) :=
  sorry

/-- Membership in the regular-section submonoid of an affine étale object is membership
in the nonzerodivisors of the same ring of sections. -/
theorem mem_regularStructureSections_iff_mem_nonZeroDivisors
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
    (s : (commStructureSheafLift X).obj.obj (op U.obj)) :
    s ∈ (regularStructureSections X).obj (op U.obj) ↔
      s ∈ nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)) :=
  sorry

/-- Membership in the regular-section submonoid of an affine étale object is equivalent
to the underlying unlifted section being a nonzerodivisor of `Γ(U, 𝒪_U)`. -/
theorem mem_regularStructureSections_iff_down_mem_nonZeroDivisors
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
    (s : (commStructureSheafLift X).obj.obj (op U.obj)) :
    s ∈ (regularStructureSections X).obj (op U.obj) ↔
      s.down ∈ nonZeroDivisors Γ((smallEtaleToScheme X).obj U.obj, ⊤) :=
  sorry

/-- An étale section of `𝒪_X` over an affine étale object is regular if and only if it
is a nonzerodivisor of the corresponding ring of sections. -/
theorem isRegularEtaleSection_iff_mem_nonZeroDivisors
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : affineEtaleSite X}
    (s : (commStructureSheafLift X).obj.obj (op U.obj)) :
    IsRegularEtaleSection s ↔
      s ∈ nonZeroDivisors ((commStructureSheafLift X).obj.obj (op U.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
