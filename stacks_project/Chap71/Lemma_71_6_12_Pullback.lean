/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Inverse images of closed subspaces and defined pullbacks of Cartier divisors

The inverse image of a closed subspace along a morphism of algebraic spaces is
the fibre-product closed subspace, and the pullback of an effective Cartier
divisor is defined when that inverse image is itself effective Cartier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The inclusion of a closed subspace is a closed immersion. -/
instance instIsClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : IsClosedImmersion Z.ι :=
  Z.isClosedImmersion

/-- The inverse image of a closed subspace along a morphism of algebraic spaces. -/
noncomputable def inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) : ClosedSubspace Y :=
  ofι (inverseImageι f Z.ι)

/-- The inclusion of an inverse image is the unbundled inverse-image immersion. -/
theorem inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImage f).ι = inverseImageι f Z.ι :=
  sorry

/-- An inverse-image closed subspace is the fibre-product closed immersion
`inverseImageι f Z.ι`. -/
theorem inverseImage_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImage f).ι = inverseImageι f Z.ι ∧
      IsClosedImmersion (Z.inverseImage f).ι :=
  sorry

/-- The pullback of a closed subspace by `f` is defined when the inverse image is
an effective Cartier divisor. -/
abbrev pullbackDefined {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) : Prop :=
  IsEffectiveCartierDivisor (Z.inverseImage f).ι

/-- Definedness of the pullback is effective Cartier-ness of the inverse image. -/
theorem pullbackDefined_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    Z.pullbackDefined f ↔ IsEffectiveCartierDivisor (Z.inverseImage f).ι :=
  sorry

/-- The kernel ideal of an inverse image is the inverse-image ideal sheaf. -/
theorem inverseImage_idealSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (Z : ClosedSubspace X) (f : Y ⟶ X) :
    (Z.inverseImage f).idealSheaf = Z.idealSheaf.pullback f :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
