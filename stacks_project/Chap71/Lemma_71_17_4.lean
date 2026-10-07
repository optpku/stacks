module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Lemma 71.17.4

A chosen blowup of a closed subspace of an algebraic space is an isomorphism
over the complement of the center, its exceptional divisor is an effective
Cartier divisor, and the twist module `𝒪(-1)` is canonically identified with
the associated sheaf of that divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.4 (1): for a scheme `S`, an algebraic space `X` over `S`, a closed
subspace `Z ⊂ X`, and a chosen blowup `π : along Z`, the restriction
`openInverseImageTo π.hom (closedImmersionComplementι Z.ι)` of the blowup
morphism, i.e. `b|_{b⁻¹(X \ Z)} : b⁻¹(X \ Z) ⟶ X \ Z`, is an isomorphism. -/
@[stacks 085T, instance]
instance instIsIso_openInverseImageTo_centerComplement
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) :
    IsIso (openInverseImageTo π.hom (closedImmersionComplementι Z.ι)) :=
  sorry

/-- Lemma 71.17.4 (2): the exceptional divisor `exceptionalDivisor π`, which is
the inverse image `E = b⁻¹(Z)` of the center, is an effective Cartier divisor
on the blowup space. -/
@[stacks 085T, instance]
instance instIsEffectiveCartierDivisor_exceptionalDivisor
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) :
    IsEffectiveCartierDivisor (exceptionalDivisor π).ι :=
  sorry

/-- Lemma 71.17.4 (3): there is a canonical identification of the twist
`π.reesTwist.twistModule (-1)`, written `𝒪_{X'}(-1)`, with the associated
sheaf `ClosedSubspace.associatedSheaf (exceptionalDivisor π)`, written
`𝒪_{X'}(E)`. -/
@[stacks 085T]
theorem isIsomorphic_twistNegOne_associatedSheaf
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) [IsEffectiveCartierDivisor (exceptionalDivisor π).ι] :
    IsIsomorphic (π.reesTwist.twistModule (-1))
      (ClosedSubspace.associatedSheaf (exceptionalDivisor π)) :=
  sorry

/-- The blowup morphism is an isomorphism over the open complement of the
center. -/
theorem isIsoOverOpen_centerComplement
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) :
    IsIsoOverOpen π.hom (closedImmersionComplementι Z.ι) :=
  sorry

/-- The ideal sheaf of the exceptional divisor is isomorphic to the first
twist module `𝒪_{X'}(1)`. -/
theorem isIsomorphic_exceptionalIdeal_twistOne
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) [IsEffectiveCartierDivisor (exceptionalDivisor π).ι] :
    IsIsomorphic (Hom.idealSheaf (exceptionalDivisor π).ι)
      (π.reesTwist.twistModule 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
