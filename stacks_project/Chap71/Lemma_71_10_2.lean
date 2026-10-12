/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap71.Definition_71_10_1_MeromorphicFunction

/-!
# Lemma 71.10.2

On an affine scheme étale over an algebraic space `X`, the regular-section
submonoid `S_X(U)` is the set of nonzerodivisors of `𝒪_X(U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.2: for a scheme `S` and an algebraic space `X` over `S`, if `U` is affine
and étale over `X`, then `(regularStructureSections X).obj (op U.obj)` is the set of
nonzerodivisors of `(commStructureSheafLift X).obj.obj (op U.obj)`. -/
@[stacks 0EN4]
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
