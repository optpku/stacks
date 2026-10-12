/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty

/-!
# Transfer of the resolution property along quasi-affine morphisms

A quasi-affine morphism of algebraic spaces transfers the resolution property from
a quasi-compact quasi-separated target to the source. The affine case is the
corresponding special case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
quasi-affine morphism `f : X ⟶ Y` of algebraic spaces transfers the resolution property
to `X`. -/
theorem hasResolutionProperty_of_quasiAffine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiAffine f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : HasResolutionProperty Y) : HasResolutionProperty X := sorry

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then an
affine morphism `f : X ⟶ Y` of algebraic spaces transfers the resolution property to
`X`. -/
theorem hasResolutionProperty_of_affine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : HasResolutionProperty Y) : HasResolutionProperty X := sorry

end AlgebraicGeometry.AlgebraicSpace
