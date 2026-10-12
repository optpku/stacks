/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Lemma 71.17.9

The pullback of every effective Cartier divisor along a blowup morphism of
algebraic spaces is defined.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.9: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `π : Blowup X I` be a blowup of `X` in a closed subspace, equivalently
`π : along Z` for a closed subspace `Z ⊂ X`. For any effective Cartier divisor
`D` on `X`, the pullback `b⁻¹D` is defined in the sense of
`ClosedSubspace.pullbackDefined`, i.e. `D.pullbackDefined π.hom`. -/
@[stacks 085X]
theorem pullbackDefined {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    D.pullbackDefined π.hom :=
  sorry

/-- The inverse image of an effective Cartier divisor along a blowup morphism
of algebraic spaces is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_inverseImage
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] :
    IsEffectiveCartierDivisor (D.inverseImage π.hom).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
